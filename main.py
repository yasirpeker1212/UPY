import os
import subprocess
import webbrowser
import tkinter as tk
from pathlib import Path
import threading
import time
from concurrent.futures import ThreadPoolExecutor, as_completed
from themes import themes
from datetime import datetime
import json
import functools
import requests,shlex 

# Try to import PIL, fallback gracefully if not available
try:
    from PIL import Image, ImageTk
    PIL_AVAILABLE = True
except ImportError:
    PIL_AVAILABLE = False

try:
    import configparser
    CONFIGPARSER_AVAILABLE = True
except ImportError:
    CONFIGPARSER_AVAILABLE = False

# Constants
UPY_DIR = Path.home() / ".upy"
THEME_FILE = UPY_DIR / "theme.upl"
CACHE_FILE = UPY_DIR / "file_cache.json"
LANGUAGE_FILE = UPY_DIR / "language.upl"
MAX_SEARCH_RESULTS = 8
DEBOUNCE_DELAY = 150  # ms
INDEX_CHUNK_SIZE = 10000

# Language support
LANGUAGES = {
    'en': {
        'search_google_for': 'Search Google for',
        'search_duckduckgo_for': 'Search DuckDuckGo for',
        'create_folder_called': 'Create a Folder Called',
        'create_file_called': 'Create a File Called',
        'date_is': 'Date is',
        'time_is': 'Time is',
        'app_not_found': 'App \'{}\' not found',
        'error': 'Error',
        'language_changed_to': 'Language changed to English',
        'available_languages': 'Available languages: English (en), Turkish (tr)',
        'indexing_files': 'Indexed {} files',
        'error_loading_theme': 'Error loading saved theme',
        'error_saving_theme': 'Error saving theme',
        'error_building_index': 'Error building file index',
        'previewing_theme': 'UPL - Previewing: {}',
        'months': ['January', 'February', 'March', 'April', 'May', 'June',
                  'July', 'August', 'September', 'October', 'November', 'December'],
        'date_format': "%d %B %Y",
        'time_format': "%I:%M %p"
    },
    'tr': {
        'search_google_for': 'Google\'da ara',
        'search_duckduckgo_for': 'DuckDuckGo\'da ara',
        'create_folder_called': 'Klasör oluştur',
        'create_file_called': 'Dosya oluştur',
        'date_is': 'Tarih',
        'time_is': 'Saat',
        'app_not_found': '\'{}\' uygulaması bulunamadı',
        'error': 'Hata',
        'language_changed_to': 'Dil Türkçe olarak değiştirildi',
        'available_languages': 'Mevcut diller: İngilizce (en), Türkçe (tr)',
        'indexing_files': '{} dosya indekslendi',
        'error_loading_theme': 'Kaydedilen tema yüklenirken hata',
        'error_saving_theme': 'Tema kaydedilirken hata',
        'error_building_index': 'Dosya indeksi oluşturulurken hata',
        'previewing_theme': 'UPL - Önizleme: {}',
        'months': ['Ocak', 'Şubat', 'Mart', 'Nisan', 'Mayıs', 'Haziran',
                  'Temmuz', 'Ağustos', 'Eylül', 'Ekim', 'Kasım', 'Aralık'],
        'date_format': "%d %B %Y",
        'time_format': "%H:%M"
    }
}

# Ensure UPY directory exists
UPY_DIR.mkdir(exist_ok=True)

def load_saved_language():
    """Load the saved language from file"""
    try:
        if LANGUAGE_FILE.exists():
            content = LANGUAGE_FILE.read_text().strip()
            if content in LANGUAGES:
                return content
    except Exception as e:
        print(f"Error loading saved language: {e}")
    return "en"  # Default language

def save_language(lang_code):
    """Save language to file"""
    try:
        LANGUAGE_FILE.write_text(lang_code)
    except Exception as e:
        print(f"Error saving language: {e}")

# Initialize current language from saved file
current_language = load_saved_language()

def get_text(key):
    """Get localized text"""
    return LANGUAGES[current_language].get(key, key)

def format_date():
    """Format date according to current language"""
    now = datetime.now()
    if current_language == 'tr':
        # Turkish month names
        months_tr = get_text('months')
        month_name = months_tr[now.month - 1]
        return f"{now.day} {month_name} {now.year}"
    else:
        return now.strftime(get_text('date_format'))

def format_time():
    """Format time according to current language"""
    now = datetime.now()
    return now.strftime(get_text('time_format'))

@functools.lru_cache(maxsize=128)
def get_file_type_icon(extension):
    """Get icon for file type with caching"""
    icon_map = {
        '.txt': '📄', '.pdf': '📋', '.doc': '📝', '.docx': '📝',
        '.jpg': '🖼️', '.png': '🖼️', '.gif': '🖼️', '.mp4': '🎬',
        '.mp3': '🎵', '.py': '🐍', '.js': '📜', '.html': '🌐',
        '.zip': '📦', '.deb': '📦', '.exe': '⚙️'
    }
    return icon_map.get(extension.lower(), '📄')

def load_saved_theme():
    """Load the saved theme from file"""
    try:
        if THEME_FILE.exists():
            content = THEME_FILE.read_text().strip()
            if content:
                # Parse the theme data to find the theme name
                for theme_name, theme_data in themes.items():
                    if str(theme_data) == content:
                        return theme_name
    except Exception as e:
        print(get_text('error_loading_theme') + f": {e}")
    return "gruvbox"  # Default theme

# Initialize current theme from saved file
current_theme = load_saved_theme()

class OptimizedFileIndexer:
    """Highly optimized file indexer with caching and smart limits"""
    
    def __init__(self):
        self.file_index = {}
        self.indexed = False
        self.indexing_lock = threading.Lock()
        self.max_depth = 3  # Reduced depth
        self.max_files = 500  # Reduced file count
        self.cache_duration = 3600  # 1 hour cache
        
        # Optimized ignore patterns
        self.ignored_patterns = {
            '.git', '.svn', '.hg', '__pycache__', '.cache', 
            'node_modules', '.npm', '.venv', 'venv', '.local/share/Trash',
            'snap', '.steam', '.wine', '.cargo', '.rustup'
        }
        
        # Priority file extensions (most commonly searched)
        self.priority_extensions = {
            '.txt', '.pdf', '.doc', '.docx', '.py', '.js', '.html', '.css',
            '.jpg', '.png', '.mp4', '.mp3', '.zip'
        }
        
        # Try to load from cache first
        if self._load_cache():
            self.indexed = True
        else:
            # Start indexing in background with lower priority
            threading.Thread(target=self._build_index, daemon=True).start()
    
    def _load_cache(self):
        """Load file index from cache if valid"""
        try:
            if CACHE_FILE.exists():
                cache_data = json.loads(CACHE_FILE.read_text())
                if time.time() - cache_data.get('timestamp', 0) < self.cache_duration:
                    self.file_index = cache_data.get('index', {})
                    return len(self.file_index) > 0
        except Exception:
            pass
        return False
    
    def _save_cache(self):
        """Save file index to cache"""
        try:
            cache_data = {
                'timestamp': time.time(),
                'index': self.file_index
            }
            CACHE_FILE.write_text(json.dumps(cache_data, separators=(',', ':')))
        except Exception:
            pass
    
    def _should_index_file(self, filepath):
        """Optimized file filtering"""
        try:
            if filepath.is_symlink():
                return False
            
            stat = filepath.stat()
            # Skip very large files (>50MB) and very small files
            if stat.st_size > 50 * 1024 * 1024 or stat.st_size == 0:
                return False
            
            # Skip recently accessed system files
            if time.time() - stat.st_atime > 30 * 24 * 3600:  # 30 days
                return False
            
            ext = filepath.suffix.lower()
            return ext in self.priority_extensions or not ext
        except (OSError, PermissionError):
            return False
    
    def _should_skip_dir(self, dir_path):
        """Optimized directory filtering"""
        dir_name = dir_path.name
        return (dir_name.startswith('.') and dir_name not in {'.config'}) or \
               any(pattern in dir_name for pattern in self.ignored_patterns)
    
    def _build_index(self):
        """Build file index with improved performance"""
        with self.indexing_lock:
            if self.indexed:
                return
            
            home_path = Path.home()
            file_count = 0
            processed_dirs = set()
            
            try:
                # Process high-priority directories first
                priority_dirs = ['Desktop', 'Documents', 'Downloads', 'Pictures']
                
                for priority_dir in priority_dirs:
                    if file_count >= self.max_files:
                        break
                    
                    dir_path = home_path / priority_dir
                    if dir_path.exists() and dir_path not in processed_dirs:
                        file_count = self._index_directory(dir_path, file_count, 2)
                        processed_dirs.add(dir_path)
                
                # Process remaining directories
                if file_count < self.max_files:
                    for item in home_path.iterdir():
                        if file_count >= self.max_files:
                            break
                        
                        if item.is_dir() and item not in processed_dirs:
                            if not self._should_skip_dir(item):
                                file_count = self._index_directory(item, file_count, 1)
                
                self._save_cache()
                self.indexed = True
                print(get_text('indexing_files').format(file_count))
                
            except Exception as e:
                print(get_text('error_building_index') + f": {e}")
    
    def _index_directory(self, dir_path, file_count, max_depth):
        """Index a single directory recursively"""
        if file_count >= self.max_files or max_depth <= 0:
            return file_count
        
        try:
            items = list(dir_path.iterdir())
            # Sort to prioritize recently modified files
            items.sort(key=lambda x: x.stat().st_mtime if x.exists() else 0, reverse=True)
            
            for item in items[:50]:  # Limit items per directory
                if file_count >= self.max_files:
                    break
                
                if item.is_file() and self._should_index_file(item):
                    key = item.name.lower()
                    if key not in self.file_index:
                        self.file_index[key] = []
                    
                    self.file_index[key].append({
                        'name': item.name,
                        'path': str(item),
                        'dir': str(item.parent.relative_to(Path.home())),
                        'size': item.stat().st_size,
                        'icon': get_file_type_icon(item.suffix)
                    })
                    file_count += 1
                    
                elif item.is_dir() and not self._should_skip_dir(item):
                    file_count = self._index_directory(item, file_count, max_depth - 1)
                    
        except (PermissionError, OSError):
            pass
        
        return file_count
    
    @functools.lru_cache(maxsize=64)
    def search_files(self, query, max_results=MAX_SEARCH_RESULTS):
        """Cached file search with relevance scoring"""
        if not self.indexed or not query or len(query) < 2:
            return []
        
        query_lower = query.lower()
        results = []
        
        # Score-based matching
        for filename_key, files in self.file_index.items():
            if len(results) >= max_results * 2:  # Get more for sorting
                break
            
            # Calculate relevance score
            score = 0
            if filename_key.startswith(query_lower):
                score += 10  # Prefix match is highest priority
            elif query_lower in filename_key:
                score += 5   # Contains match
            else:
                continue
            
            for file_info in files:
                if len(results) >= max_results * 2:
                    break
                
                # Boost score for files in important directories
                if any(important in file_info['dir'] for important in ['Desktop', 'Documents', 'Downloads']):
                    score += 2
                
                results.append((score, file_info))
        
        # Sort by score and return top results
        results.sort(key=lambda x: x[0], reverse=True)
        return [item[1] for item in results[:max_results]]

class OptimizedIconManager:
    def __init__(self):
        self.desktop_cache = {}
        self.loaded = False

        if CONFIGPARSER_AVAILABLE:
            threading.Thread(target=self._load_desktop_files, daemon=True).start()

    def _load_desktop_files(self):
        desktop_dirs = [
            "/usr/share/applications",
            "/usr/local/share/applications",
            str(Path.home() / ".local/share/applications"),
            "/var/lib/snapd/desktop/applications",
            str(Path.home() / ".local/share/flatpak/exports/share/applications"),
        ]

        for desktop_dir in desktop_dirs:
            if os.path.exists(desktop_dir):
                try:
                    files = [f for f in os.listdir(desktop_dir) if f.endswith('.desktop')]
                    for file in files:
                        self._parse_desktop_file(os.path.join(desktop_dir, file))
                except (PermissionError, OSError):
                    continue

        self.loaded = True


    def _parse_desktop_file(self, filepath):
        try:
            config = configparser.ConfigParser()
            config.read(filepath, encoding='utf-8')

            if 'Desktop Entry' in config:
                entry = config['Desktop Entry']
                if (entry.get('Type') == 'Application' and
                    not entry.get('Hidden', '').lower() == 'true'):

                    name = entry.get('Name', '')
                    exec_cmd = entry.get('Exec', '')

                    if exec_cmd and name:
                        parts = shlex.split(exec_cmd)
                        exec_name = None

                        # Eğer flatpak run komutu var ise
                        if parts[0].endswith('flatpak') and 'run' in parts:
                            # 'run' kelimesinin indexini bul
                            run_index = parts.index('run')
                            # run'dan sonraki argümanları al
                            after_run = parts[run_index+1:]

                            # Uygulama ID'si genellikle args arasında olur
                            # --command, --branch gibi argümanlar ve uygulama id'si var
                            # Uygulama ID'si genellikle --option olmayan ilk argüman
                            for arg in after_run:
                                if not arg.startswith('--'):
                                    exec_name = arg
                                    break

                        # Eğer flatpak değilse veya yukarıdaki bulunmazsa fallback:
                        if exec_name is None:
                            exec_name = parts[0]
                            # sh veya bash ise iç komut kontrolü
                            if exec_name in ('sh', 'bash') and len(parts) > 2 and parts[1] == '-c':
                                inner_cmd = parts[2]
                                inner_parts = shlex.split(inner_cmd)
                                if inner_parts:
                                    exec_name = inner_parts[0]

                        exec_name = os.path.basename(exec_name)

                        # Yine real path bulmaya çalışabiliriz
                        real_path = shutil.which(exec_name)
                        if real_path:
                            exec_name = os.path.basename(real_path)

                        self.desktop_cache[exec_name] = name

        except Exception:
            pass
    def get_app_display_name(self, app_name):
        return self.desktop_cache.get(app_name, app_name)

class OptimizedLauncherApp:
    def __init__(self, root):
        self.root = root
        self.root.title("UPL")
        self.root.geometry("600x300+500+200")
        self.root.attributes('-topmost', True)
        
        # Initialize managers
        self.icon_manager = OptimizedIconManager()
        self.file_indexer = OptimizedFileIndexer()
        
        # State variables
        self.suggestions = []
        self.selected_index = 0
        self.previewing_theme = False
        self.original_theme = current_theme
        self.last_query = ""
        self.last_update_time = 0
        self.search_cache = {}
        self.debounce_timer = None
        
        # Initialize UI
        self._create_widgets()
        self._bind_events()
        self.apply_theme()
    
    def _create_widgets(self):
        """Create UI widgets"""
        self.entry = tk.Entry(self.root, font=("Fira Code", 18), bd=0)
        self.entry.pack(fill=tk.X, padx=10, pady=(10, 0))
        self.entry.focus_set()
        
        self.listbox = tk.Listbox(self.root, font=("Fira Code", 12), 
                                 activestyle='none', highlightthickness=0, bd=0)
        self.listbox.pack(fill=tk.BOTH, expand=True, padx=10, pady=(5, 10))
    
    def _bind_events(self):
        """Bind all events efficiently"""
        # Entry events
        events = [
            ("<Return>", self.handle_input),
            ("<Escape>", self.handle_escape),
            ("<KeyRelease>", self.key_release_handler),
            ("<Down>", self.move_down),
            ("<Up>", self.move_up),
            ("<Right>", self.handle_right_arrow),
            ("<Left>", self.handle_left_arrow),
            ("<Control-a>", self.select_all),
            ("<Control-c>", self.copy_selection),
            ("<Control-v>", self.paste_clipboard),
            ("<Control-x>", self.cut_selection)
        ]
        
        for event, handler in events:
            self.entry.bind(event, handler)
        
        # Listbox events
        self.listbox.bind("<Button-1>", self.on_listbox_click)
        self.listbox.bind("<Double-Button-1>", self.on_listbox_double_click)
    
    def save_theme(self, theme_name):
        """Save theme efficiently"""
        try:
            THEME_FILE.write_text(str(themes[theme_name]))
        except Exception as e:
            print(get_text('error_saving_theme') + f": {e}")
    
    def apply_theme(self):
        """Apply theme with minimal operations"""
        theme = themes[current_theme]
        
        # Batch configure operations
        self.root.configure(bg=theme["bg"])
        self.entry.configure(
            bg=theme["entry_bg"], 
            fg=theme["entry_fg"], 
            insertbackground=theme["entry_fg"]
        )
        self.listbox.configure(
            bg=theme["list_bg"], 
            fg=theme["list_fg"],
            selectbackground=theme["highlight"], 
            selectforeground=theme["fg"]
        )
        
        # Save theme only if not previewing
        if not self.previewing_theme:
            self.save_theme(current_theme)
            self.root.title("UPL")
    
    def handle_escape(self, event):
        """Handle escape key"""
        if self.previewing_theme:
            self.exit_preview_mode()
        else:
            self.root.quit()
    
    def handle_right_arrow(self, event):
        """Handle right arrow for theme preview"""
        if self.is_theme_selected():
            self.preview_theme()
            return "break"
        return None
    
    def handle_left_arrow(self, event):
        """Handle left arrow to exit preview"""
        if self.previewing_theme:
            self.exit_preview_mode()
            return "break"
        return None
    
    def is_theme_selected(self):
        """Check if currently selected item is a theme"""
        if self.suggestions and 0 <= self.selected_index < len(self.suggestions):
            return self.suggestions[self.selected_index].startswith("[theme] ")
        return False
    
    def preview_theme(self):
        """Preview the selected theme"""
        if not self.is_theme_selected():
            return
        
        global current_theme
        selected = self.suggestions[self.selected_index]
        theme_name = selected[8:]  # Remove "[theme] " prefix
        
        if theme_name in themes:
            if not self.previewing_theme:
                self.original_theme = current_theme
                self.previewing_theme = True
            
            current_theme = theme_name
            self.apply_theme()
            self.root.title(get_text('previewing_theme').format(theme_name))
    
    def exit_preview_mode(self):
        """Exit theme preview mode"""
        if self.previewing_theme:
            global current_theme
            current_theme = self.original_theme
            self.previewing_theme = False
            self.apply_theme()
    
    def key_release_handler(self, event):
        """Handle key release with debouncing"""
        if event.keysym in ["Up", "Down", "Return", "Escape", "Left", "Right"]:
            return
        
        # Exit preview mode when typing
        if self.previewing_theme:
            self.exit_preview_mode()
        
        # Cancel previous timer
        if self.debounce_timer:
            self.root.after_cancel(self.debounce_timer)
        
        # Schedule new update
        self.debounce_timer = self.root.after(DEBOUNCE_DELAY, self.update_suggestions)
    
    def select_all(self, event=None):
        """Select all text"""
        self.entry.selection_range(0, tk.END)
        return "break"
    
    def copy_selection(self, event=None):
        """Copy selected text"""
        try:
            self.root.clipboard_clear()
            self.root.clipboard_append(self.entry.selection_get())
        except:
            pass
        return "break"
    
    def paste_clipboard(self, event=None):
        """Paste from clipboard"""
        try:
            self.entry.insert(tk.INSERT, self.root.clipboard_get())
        except:
            pass
        return "break"
    
    def cut_selection(self, event=None):
        """Cut selected text"""
        try:
            self.copy_selection()
            start = self.entry.index(tk.SEL_FIRST)
            end = self.entry.index(tk.SEL_LAST)
            self.entry.delete(start, end)
        except:
            pass
        return "break"
    
    def move_down(self, event):
        """Move selection down"""
        if self.suggestions and self.selected_index < len(self.suggestions) - 1:
            self.selected_index += 1
            self.update_selection()
            
            if self.previewing_theme and self.is_theme_selected():
                self.preview_theme()
        return "break"
    
    def move_up(self, event):
        """Move selection up"""
        if self.suggestions and self.selected_index > 0:
            self.selected_index -= 1
            self.update_selection()
            
            if self.previewing_theme and self.is_theme_selected():
                self.preview_theme()
        return "break"
    
    def update_selection(self):
        """Update selection efficiently"""
        if not self.suggestions:
            return
        
        self.listbox.selection_clear(0, tk.END)
        self.listbox.selection_set(self.selected_index)
        self.listbox.activate(self.selected_index)
        self.listbox.see(self.selected_index)
    
    def on_listbox_click(self, event):
        """Handle listbox click"""
        selection = self.listbox.curselection()
        if selection:
            self.selected_index = selection[0]
            self.update_selection()
    
    def on_listbox_double_click(self, event):
        """Handle listbox double-click"""
        selection = self.listbox.curselection()
        if selection:
            self.selected_index = selection[0]
            self.handle_input()
    
    def update_suggestions(self):
        """Update suggestions with caching"""
        query = self.entry.get().strip()
        
        if query == self.last_query:
            return
        
        self.last_query = query
        
        if not query:
            self.suggestions = []
            self.listbox.delete(0, tk.END)
            return
        
        # Check cache first
        cache_key = f"{query}_{current_language}"
        if cache_key in self.search_cache:
            self.suggestions = self.search_cache[cache_key]
        else:
            self.suggestions = self._build_suggestions(query)
            # Cache short queries
            if len(query) <= 8 and len(self.search_cache) < 50:
                self.search_cache[cache_key] = self.suggestions.copy()
        
        self._update_listbox()
        self.selected_index = 0
        self.update_selection()
    
    def _build_suggestions(self, query):
        """Build suggestions efficiently"""
        suggestions = []
        query_lower = query.lower()
        
        # Language command
        if query.startswith("!lang"):
            if len(query) > 5:
                lang_code = query[5:].strip()
                if lang_code in LANGUAGES:
                    return [f"[lang] {lang_code}"]
                else:
                    return [f"[info] {get_text('available_languages')}"]
            else:
                return [f"[info] {get_text('available_languages')}"]
        
        # Special commands
        if query == "!themes":
            return [f"[theme] {name}" for name in themes]
        
        # Quick commands
        commands = [
            ("!g", get_text('search_google_for')),
            ("!duck", get_text('search_duckduckgo_for')),
            ("!mkdir", get_text('create_folder_called')),
            ("!touch", get_text('create_file_called'))
        ]
        
        for cmd, desc in commands:
            if query.startswith(cmd) and len(query) > len(cmd):
                suggestions.append(f"{desc} '{query[len(cmd):].strip()}'")
        
        # Date/time commands
        if query.startswith("!date"):
            date_str = format_date()
            suggestions.append(f"{get_text('date_is')} '{date_str}'")
        elif query.startswith("!time"):
            time_str = format_time()
            suggestions.append(f"{get_text('time_is')} '{time_str}'")
        
        # Calculator
        if self._is_calc(query):
            try:
                result = eval(query, {"__builtins__": {}}, {})
                suggestions.append(f"{query} = {result}")
            except:
                pass
        
        # Applications (limit to most relevant)
        if len(query) >= 2:
            suggestions.extend(self._find_applications(query))
        
        # Files
        if len(query) >= 2:
            suggestions.extend(self._find_files(query))
        
        return suggestions[:MAX_SEARCH_RESULTS]
    
    def _find_applications(self, query):
        """Find applications efficiently"""
        suggestions = []
        query_lower = query.lower()
        found_apps = set()
        
        # Check common application directories
        app_dirs = [d for d in os.environ.get("PATH", "").split(":") 
                   if d and os.path.isdir(d)][:8]  # Limit directories
        
        for app_dir in app_dirs:
            if len(suggestions) >= 4:  # Limit app suggestions
                break
            
            try:
                for file in os.listdir(app_dir):
                    if len(suggestions) >= 4:
                        break
                    
                    if (file not in found_apps and 
                        not file.startswith('.') and
                        (file.lower().startswith(query_lower) or query_lower in file.lower())):
                        
                        found_apps.add(file)
                        display_name = self.icon_manager.get_app_display_name(file)
                        if display_name != file:
                            suggestions.append(f"[app] {file}|{display_name}")
                        else:
                            suggestions.append(f"[app] {file}")
            except (PermissionError, OSError):
                continue
        
        return suggestions
    
    def _find_files(self, query):
        """Find files using indexer"""
        files = self.file_indexer.search_files(query, max_results=4)
        suggestions = []
        
        for file_info in files:
            suggestions.append(f"[file] {file_info['name']}|{file_info['path']}|{file_info['dir']}|{file_info['icon']}")
        
        return suggestions
    
    def _update_listbox(self):
        """Update listbox with formatted suggestions"""
        self.listbox.delete(0, tk.END)
        
        for suggestion in self.suggestions:
            display_text = self._format_suggestion(suggestion)
            self.listbox.insert(tk.END, display_text)
    
    def _format_suggestion(self, suggestion):
        """Format suggestion for display"""
        if suggestion.startswith("[app] "):
            app_info = suggestion[6:]
            if '|' in app_info:
                app_name, display_name = app_info.split('|', 1)
                return f"📱 {display_name}"
            return f"📱 {app_info}"
        
        elif suggestion.startswith("[file] "):
            file_info = suggestion[7:]
            if '|' in file_info:
                parts = file_info.split('|')
                filename = parts[0]
                directory = parts[2] if len(parts) > 2 else 'home'
                icon = parts[3] if len(parts) > 3 else '📄'
                return f"{icon} {filename} ({directory})"
            return f"📄 {file_info}"
        
        elif suggestion.startswith("[theme] "):
            return f"🎨 {suggestion[8:]}"
        
        elif suggestion.startswith("[lang] "):
            lang_code = suggestion[7:]
            lang_name = "English" if lang_code == "en" else "Türkçe"
            return f"🌐 {lang_name} ({lang_code})"
        
        elif suggestion.startswith("[info] "):
            return f"ℹ️ {suggestion[7:]}"
        
        elif get_text('search_google_for') in suggestion:
            return f"🔍 {suggestion}"
        elif get_text('search_duckduckgo_for') in suggestion:
            return f"🦆 {suggestion}"
        elif get_text('date_is') in suggestion:
            return f"📅 {suggestion}"
        elif get_text('time_is') in suggestion:
            return f"⌚ {suggestion}"
        elif "=" in suggestion:
            return f"🧮 {suggestion}"
        elif get_text('create_folder_called') in suggestion:
            return f"📁 {suggestion}"
        elif get_text('create_file_called') in suggestion:
            return f"📄 {suggestion}"
        
        return suggestion
    
    def _is_calc(self, expr):
        """Check if expression is a calculator query"""
        if not expr or len(expr) > 50:
            return False
        
        try:
            allowed_chars = set('0123456789+-*/.() ')
            if not all(c in allowed_chars for c in expr):
                return False
            eval(expr, {"__builtins__": {}}, {})
            return True
        except:
            return False
    
    def handle_input(self, event=None):
        """Handle input execution"""
        if self.suggestions:
            selected = self.suggestions[self.selected_index]
            
            if selected.startswith("[lang] "):
                self._change_language(selected[7:])
                return
            elif get_text('search_google_for') in selected:
                search_term = self.entry.get()[2:] if self.entry.get().startswith("!g") else self.entry.get()
                webbrowser.open(f"https://www.google.com/search?q={search_term}")
            elif get_text('search_duckduckgo_for') in selected:
                search_term = self.entry.get()[5:] if self.entry.get().startswith("!duck") else self.entry.get()
                webbrowser.open(f"https://www.duckduckgo.com/search?q={search_term}")
            elif get_text('create_folder_called') in selected:
                folder_name = self.entry.get()[6:].strip() if self.entry.get().startswith("!mkdir") else "new_folder"
                os.makedirs(folder_name, exist_ok=True)
            elif get_text('create_file_called') in selected:
                file_name = self.entry.get()[6:].strip() if self.entry.get().startswith("!touch") else "new_file.txt"
                Path(file_name).touch()
            elif selected.startswith("[file] "):
                self._open_file(selected)
            elif selected.startswith("[theme] "):
                self._apply_theme(selected[8:])
                return
            elif selected.startswith("[app] "):
                self._launch_app(selected)
            elif selected.startswith("[info] "):
                self._show_popup(selected[7:])
                return
            elif "=" in selected:
                self._show_popup(selected)
            else:
                self._launch_app(selected)
        else:
            query = self.entry.get().strip()
            if query.startswith("?"):
                webbrowser.open(f"https://www.google.com/search?q={query[1:]}")
            elif self._is_calc(query):
                self._calculate(query)
            else:
                self._launch_app(query)
        
        self.root.quit()
    
    def _change_language(self, lang_code):
        """Change application language"""
        global current_language
        if lang_code in LANGUAGES:
            current_language = lang_code
            save_language(lang_code)
            # Clear cache to refresh suggestions with new language
            self.search_cache.clear()
            # Show confirmation message
            self._show_popup(get_text('language_changed_to'))
    
    def _open_file(self, selected):
        """Open selected file"""
        file_info = selected[7:]
        if '|' in file_info:
            parts = file_info.split('|')
            filepath = parts[1] if len(parts) > 1 else parts[0]
            subprocess.Popen(['xdg-open', filepath])
    
    def _apply_theme(self, theme_name):
        """Apply selected theme"""
        global current_theme
        current_theme = theme_name
        self.previewing_theme = False
        self.apply_theme()
        self.entry.delete(0, tk.END)
        self.suggestions = []
        self.listbox.delete(0, tk.END)
    
    def _launch_app(self, app_or_selected):
        """Launch application"""
        if isinstance(app_or_selected, str) and app_or_selected.startswith("[app] "):
            app_info = app_or_selected[6:]
            app_name = app_info.split('|')[0] if '|' in app_info else app_info
        else:
            app_name = app_or_selected
        
        try:
            subprocess.Popen([app_name])
        except FileNotFoundError:
            self._show_popup(get_text('app_not_found').format(app_name))
    
    def _calculate(self, expr):
        """Calculate expression"""
        try:
            result = eval(expr, {"__builtins__": {}}, {})
            self._show_popup(f"{expr} = {result}")
        except Exception as e:
            self._show_popup(f"{get_text('error')}: {e}")
    
    def _show_popup(self, text):
        """Show popup message"""
        popup = tk.Toplevel(self.root)
        popup.geometry("400x100+550+260")
        popup.configure(bg=themes[current_theme]["bg"])
        
        label = tk.Label(popup, text=text, font=("Fira Code", 16), 
                        fg=themes[current_theme]["fg"], 
                        bg=themes[current_theme]["bg"])
        label.pack(padx=10, pady=20)
        
        self.root.after(3000, popup.destroy)
def center_window(window):
    window.update_idletasks()  # Update "requested size" from geometry manager
    width = window.winfo_width()
    height = window.winfo_height()
    screen_width = window.winfo_screenwidth()
    screen_height = window.winfo_screenheight()
    x = (screen_width - width) // 2
    y = (screen_height - height) // 2
    window.geometry(f"{width}x{height}+{x}+{y}")

if __name__ == "__main__":
    root = tk.Tk()
    app = OptimizedLauncherApp(root)
    root.geometry("600x400+300+200")
    center_window(root)
    root.mainloop()
