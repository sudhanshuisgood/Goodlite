#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
goodlite Editor - a lightweight, fast code editor with a built-in terminal.

* Pure standard library (Tkinter) -> tiny RAM footprint (~25-40 MB), instant start.
* Regex-based syntax highlighting for 20 languages (debounced, viewport-aware
  for big files so typing never lags).
* Tabbed editing, Open / Save / Save As / New, dark + light themes.
* Built-in terminal: F5 runs the current file and streams live output / errors,
  and the input box sends text to the running program (stdin) or, when nothing
  is running, executes shell commands.

Requires Python 3.8+ (Windows 10 / 11, also works on Linux / macOS).
"""

import bisect
import codecs
import os
import queue
import re
import shlex
import shutil
import signal
import subprocess
import sys
import tempfile
import threading
import time
import traceback
import webbrowser
import tkinter as tk
import tkinter.font as tkfont
from tkinter import filedialog, messagebox, simpledialog, ttk

APP_NAME = "Goodlite Editor"
IS_WIN = os.name == "nt"
FROZEN = getattr(sys, "frozen", False)          # True when running as PyInstaller .exe
CREATE_NO_WINDOW = 0x08000000                   # hide the console window of child processes

FULL_HL_LINES = 4000      # files up to this many lines are highlighted completely
HL_MARGIN = 150           # for bigger files: lines highlighted above/below the viewport
MAX_HL_CHARS = 600_000    # safety valve for absurdly long (e.g. minified) content
TERM_MAX_LINES = 5000     # terminal scrollback cap (keeps RAM low)
BIG_FILE_BYTES = 10 * 1024 * 1024


# =============================================================================
#  SYNTAX DEFINITIONS
# =============================================================================
TAGS = ["comment", "string", "keyword", "type", "number", "func",
        "special", "attr", "tag", "variable", "heading", "bold"]


def _kw(words):
    """Whole-word alternation regex from a space separated word list."""
    return r"\b(?:" + "|".join(re.escape(w) for w in words.split()) + r")\b"


STR_DQ = r'"(?:\\.|[^"\\\n])*"'
STR_SQ = r"'(?:\\.|[^'\\\n])*'"
STR_C = STR_DQ + "|" + STR_SQ
NUM_C = (r"\b(?:0[xX][0-9a-fA-F_]+|0[bB][01_]+|"
         r"\d[\d_]*(?:\.\d+)?(?:[eE][+-]?\d+)?)[uUlLfFdD]*\b")
CMT_LINE = r"//[^\n]*"
CMT_BLOCK = r"/\*[\s\S]*?(?:\*/|\Z)"
FUNC = r"\b[A-Za-z_]\w*(?=[ \t]*\()"
PREPROC = r"^[ \t]*#[^\n]*"


def _clike(kw, types="", pre=(), strings=STR_C, line=CMT_LINE, block=CMT_BLOCK,
           number=NUM_C, post=()):
    rules = []
    if block:
        rules.append(("comment", block))
    if line:
        rules.append(("comment", line))
    rules += list(pre)
    rules.append(("string", strings))
    rules.append(("number", number))
    rules += list(post)
    rules.append(("keyword", _kw(kw)))
    if types:
        rules.append(("type", _kw(types)))
    rules.append(("func", FUNC))
    return rules


# language name -> dict(rules=[(tag, pattern)], flags=int, comment=str|None, exts=tuple)
LANGS = {}


def _lang(name, rules, exts=(), comment=None, flags=0):
    LANGS[name] = {"rules": rules, "flags": flags, "comment": comment, "exts": exts}


# ---- Python -----------------------------------------------------------------
_lang("Python", [
    ("comment", r"#[^\n]*"),
    ("string", r'(?:[rRbBfFuU]{0,2})(?:"""[\s\S]*?(?:"""|\Z)|\'\'\'[\s\S]*?(?:\'\'\'|\Z)|'
               r'"(?:\\.|[^"\\\n])*"|\'(?:\\.|[^\'\\\n])*\')'),
    ("special", r"^[ \t]*@[\w.]+"),
    ("number", r"\b(?:0[xX][0-9a-fA-F_]+|0[bB][01_]+|0[oO][0-7_]+|"
               r"\d[\d_]*(?:\.\d*)?(?:[eE][+-]?\d+)?j?)\b"),
    ("keyword", _kw("False None True and as assert async await break class continue def "
                    "del elif else except finally for from global if import in is lambda "
                    "nonlocal not or pass raise return try while with yield match case")),
    ("type", _kw("self cls print len range int str float list dict set tuple bool bytes "
                 "object type isinstance open super enumerate zip map filter sorted sum "
                 "min max abs input iter next any all repr format Exception ValueError "
                 "TypeError KeyError IndexError")),
    ("func", r"(?<=\bdef )\w+|(?<=\bclass )\w+"),
    ("func", FUNC),
], exts=("py", "pyw"), comment="#")

# ---- JavaScript / TypeScript --------------------------------------------------
_JS_STR = r"`(?:\\[\s\S]|[^`\\])*(?:`|\Z)|" + STR_C
_JS_KW = ("async await break case catch class const continue debugger default delete do "
          "else export extends finally for function if import in instanceof let new of "
          "return static super switch this throw try typeof var void while with yield get "
          "set from as true false null undefined NaN Infinity")
_JS_TYPES = ("console window document Object Array String Number Boolean Math JSON Promise "
             "Map Set Date RegExp Error Symbol parseInt parseFloat require module exports")
_lang("JavaScript", _clike(_JS_KW, _JS_TYPES, strings=_JS_STR),
      exts=("js", "mjs", "cjs", "jsx"), comment="//")
_lang("TypeScript", _clike(
    _JS_KW + " abstract declare enum implements interface keyof namespace private protected "
             "public readonly type is infer satisfies override",
    _JS_TYPES + " string number boolean any void never unknown object bigint symbol",
    strings=_JS_STR), exts=("ts", "tsx"), comment="//")

# ---- C / C++ / Java / C# -------------------------------------------------------
_C_KW = ("auto break case const continue default do else enum extern for goto if inline "
         "register restrict return sizeof static struct switch typedef union volatile while")
_C_TYPES = ("int char short long float double void unsigned signed size_t ssize_t bool _Bool "
            "uint8_t uint16_t uint32_t uint64_t int8_t int16_t int32_t int64_t FILE NULL "
            "true false")
_lang("C", _clike(_C_KW, _C_TYPES, pre=[("special", PREPROC)]), exts=("c", "h"), comment="//")
_lang("C++", _clike(
    _C_KW + " alignas alignof and asm catch class constexpr const_cast decltype delete "
            "dynamic_cast explicit export final friend mutable namespace new noexcept not "
            "nullptr operator or override private protected public reinterpret_cast "
            "static_assert static_cast template this throw try typeid typename using virtual",
    _C_TYPES + " string vector map set unordered_map unique_ptr shared_ptr wchar_t cout cin "
               "cerr endl std",
    pre=[("special", PREPROC)]), exts=("cpp", "cc", "cxx", "hpp", "hh", "hxx"), comment="//")
_lang("Java", _clike(
    "abstract assert break case catch class const continue default do else enum extends "
    "final finally for goto if implements import instanceof interface native new package "
    "private protected public return static strictfp super switch synchronized this throw "
    "throws transient try volatile while var record sealed permits yield true false null",
    "boolean byte char short int long float double void String Integer Long Double Boolean "
    "Object List Map Set ArrayList HashMap System Math",
    pre=[("special", r"@[A-Za-z_]\w*")],
    strings=r'"""[\s\S]*?(?:"""|\Z)|' + STR_C), exts=("java",), comment="//")
_lang("C#", _clike(
    "abstract as base break case catch checked class const continue default delegate do else "
    "enum event explicit extern finally fixed for foreach goto if implicit in interface "
    "internal is lock namespace new operator out override params private protected public "
    "readonly ref return sealed sizeof stackalloc static struct switch this throw try typeof "
    "unchecked unsafe using virtual volatile while async await var yield record init get set "
    "value when where partial true false null",
    "bool byte char decimal double float int long object sbyte short string uint ulong "
    "ushort void dynamic String List Dictionary Console Math Task",
    pre=[("special", PREPROC)],
    strings=r'@"(?:""|[^"])*"|' + STR_C), exts=("cs",), comment="//")

# ---- PHP ----------------------------------------------------------------------
_lang("PHP", [
    ("comment", CMT_BLOCK), ("comment", CMT_LINE), ("comment", r"#[^\n]*"),
    ("special", r"<\?php|<\?=|\?>"),
    ("string", STR_C),
    ("variable", r"\$[A-Za-z_]\w*"),
    ("number", NUM_C),
    ("keyword", _kw("abstract and array as break callable case catch class clone const "
                    "continue declare default do echo else elseif empty enddeclare endfor "
                    "endforeach endif endswitch endwhile eval exit die extends final finally "
                    "fn for foreach function global goto if implements include include_once "
                    "instanceof insteadof interface isset list match namespace new or print "
                    "private protected public readonly require require_once return static "
                    "switch throw trait try unset use var while xor yield true false null "
                    "self parent")),
    ("type", _kw("int float string bool void mixed object iterable")),
    ("func", FUNC),
], exts=("php", "phtml"), comment="//", flags=re.IGNORECASE)

# ---- Ruby ---------------------------------------------------------------------
_lang("Ruby", [
    ("comment", r"^=begin[\s\S]*?(?:^=end|\Z)"), ("comment", r"#[^\n]*"),
    ("string", STR_C),
    ("special", r"(?<![\w:]):[A-Za-z_]\w*[?!]?"),
    ("variable", r"@@?[A-Za-z_]\w*|\$[A-Za-z_]\w*"),
    ("number", NUM_C),
    ("keyword", _kw("alias and begin break case class def do else elsif end ensure false for "
                    "if in module next nil not or redo rescue retry return self super then "
                    "true undef unless until when while yield puts require require_relative "
                    "attr_accessor attr_reader attr_writer include extend lambda proc")),
    ("func", r"(?<=def )[\w.?!=]+"),
    ("type", r"\b[A-Z][A-Za-z0-9_]*\b"),
    ("func", FUNC),
], exts=("rb", "rake", "gemspec"), comment="#")

# ---- Go -----------------------------------------------------------------------
_lang("Go", _clike(
    "break case chan const continue default defer else fallthrough for func go goto if import "
    "interface map package range return select struct switch type var",
    "bool byte complex64 complex128 error float32 float64 int int8 int16 int32 int64 rune "
    "string uint uint8 uint16 uint32 uint64 uintptr any comparable true false nil iota append "
    "cap close copy delete len make new panic print println recover",
    strings=r"`[^`]*(?:`|\Z)|" + STR_C), exts=("go",), comment="//")

# ---- Rust ---------------------------------------------------------------------
_lang("Rust", [
    ("comment", CMT_BLOCK), ("comment", CMT_LINE),
    ("string", STR_DQ),
    ("string", r"'(?:\\(?:u\{[0-9a-fA-F]+\}|x[0-9a-fA-F]{2}|.)|[^'\\\n])'"),
    ("special", r"'[A-Za-z_]\w*\b"),
    ("special", r"#!?\[[^\]\n]*\]"),
    ("number", r"\b(?:0x[0-9a-fA-F_]+|0b[01_]+|0o[0-7_]+|\d[\d_]*(?:\.\d+)?(?:[eE][+-]?\d+)?)"
               r"(?:[iu](?:8|16|32|64|128|size)|f32|f64)?\b"),
    ("keyword", _kw("as async await break const continue crate dyn else enum extern fn for if "
                    "impl in let loop match mod move mut pub ref return self Self static "
                    "struct super trait type unsafe use where while true false")),
    ("type", _kw("bool char str u8 u16 u32 u64 u128 usize i8 i16 i32 i64 i128 isize f32 f64 "
                 "String Vec Option Result Some None Ok Err Box Rc Arc HashMap HashSet")),
    ("func", r"\b[A-Za-z_]\w*!(?=\s*[(\[{])"),
    ("func", FUNC),
], exts=("rs",), comment="//")

# ---- SQL ----------------------------------------------------------------------
_lang("SQL", [
    ("comment", r"--[^\n]*"), ("comment", CMT_BLOCK),
    ("string", r"'(?:''|[^'\n])*'"), ("string", r'"[^"\n]*"'),
    ("number", r"\b\d+(?:\.\d+)?\b"),
    ("keyword", _kw("select from where and or not insert into values update set delete create "
                    "alter drop table index view database schema primary key foreign "
                    "references unique default null check constraint join inner outer left "
                    "right full cross on as group by order having limit offset union all "
                    "distinct case when then else end in is like between exists asc desc "
                    "begin commit rollback transaction truncate add column if with recursive "
                    "over partition returning")),
    ("type", _kw("int integer bigint smallint tinyint decimal numeric float double real char "
                 "varchar text blob date datetime timestamp time boolean bool serial uuid "
                 "json jsonb")),
    ("func", FUNC),
], exts=("sql",), comment="--", flags=re.IGNORECASE)

# ---- JSON ---------------------------------------------------------------------
_lang("JSON", [
    ("comment", CMT_LINE), ("comment", CMT_BLOCK),
    ("attr", r'"(?:\\.|[^"\\\n])*"(?=\s*:)'),
    ("string", STR_DQ),
    ("number", r"-?\d+(?:\.\d+)?(?:[eE][+-]?\d+)?"),
    ("keyword", r"\b(?:true|false|null)\b"),
], exts=("json", "jsonc", "geojson"))

# ---- HTML / XML ---------------------------------------------------------------
_MARKUP_COMMON = [
    ("tag", r"</?[A-Za-z][\w:.\-]*"),
    ("tag", r"/?>"),
    ("attr", r"[A-Za-z_:@][\w:.\-]*(?=\s*=)"),
    ("string", r'(?<==)(?:"[^"]*"|\'[^\']*\')'),
]
_lang("HTML", [("comment", r"<!--[\s\S]*?(?:-->|\Z)"),
               ("special", r"<![Dd][Oo][Cc][Tt][Yy][Pp][Ee][^>]*>")] + _MARKUP_COMMON +
      [("special", r"&#?\w+;")], exts=("html", "htm", "xhtml"), comment=None)
_lang("XML", [("comment", r"<!--[\s\S]*?(?:-->|\Z)"),
              ("string", r"<!\[CDATA\[[\s\S]*?(?:\]\]>|\Z)"),
              ("special", r"<\?[\s\S]*?(?:\?>|\Z)")] + _MARKUP_COMMON +
      [("special", r"&#?\w+;")], exts=("xml", "svg", "xsl", "xslt", "xaml", "csproj", "plist"))

# ---- CSS ----------------------------------------------------------------------
_lang("CSS", [
    ("comment", CMT_BLOCK), ("string", STR_C),
    ("special", r"@[\w-]+"),
    ("number", r"#[0-9a-fA-F]{3,8}\b|(?<![\w#-])-?\d*\.?\d+(?:px|r?em|%|vh|vw|ms|s|deg|pt|fr|ch)?"),
    ("keyword", r"!important\b"),
    ("attr", r"[A-Za-z-]+(?=\s*:[^;{}\n]*[;}])"),
    ("type", r"(?<![\w-])[.#][A-Za-z_][\w-]*"),
    ("func", r"[A-Za-z-]+(?=\()"),
], exts=("css", "scss", "less"))

# ---- Markdown -----------------------------------------------------------------
_lang("Markdown", [
    ("string", r"^[ \t]*```[\s\S]*?(?:^[ \t]*```|\Z)"),
    ("heading", r"^#{1,6}[ \t].*$"),
    ("comment", r"^>.*$"),
    ("keyword", r"^[ \t]*(?:[-*+]|\d+\.)[ \t]"),
    ("bold", r"\*\*[^*\n]+\*\*|__[^_\n]+__"),
    ("string", r"`[^`\n]+`"),
    ("attr", r"\[[^\]\n]+\]\([^)\n]+\)"),
], exts=("md", "markdown"))

# ---- Bash / Shell -------------------------------------------------------------
_lang("Bash", [
    ("special", r"^#![^\n]*"),
    ("comment", r"(?<![\w$])#[^\n]*"),
    ("string", STR_DQ), ("string", r"'[^'\n]*'"),
    ("variable", r"\$(?:\w+|\{[^}\n]*\}|[?#@*!$0-9])"),
    ("number", r"\b\d+\b"),
    ("keyword", _kw("if then else elif fi for while until do done case esac in function select "
                    "time return exit break continue local export readonly declare unset "
                    "source alias")),
    ("type", _kw("echo printf read cd pwd ls cat grep sed awk test set shift trap eval exec "
                 "kill wait true false")),
    ("func", r"\b[A-Za-z_][\w-]*(?=[ \t]*\(\))"),
], exts=("sh", "bash", "zsh", "ksh"), comment="#")

# ---- YAML ---------------------------------------------------------------------
_lang("YAML", [
    ("comment", r"(?:^|(?<=\s))#[^\n]*"),
    ("special", r"^(?:---|\.\.\.)[ \t]*$"),
    ("attr", r"^[ \t]*(?:-[ \t]+)?[\w.\-/@$]+(?=[ \t]*:(?:[ \t]|$))"),
    ("string", STR_C),
    ("special", r"[&*][\w-]+"),
    ("number", r"(?<![\w.])-?\d+(?:\.\d+)?\b"),
    ("keyword", r"\b(?:true|false|null|yes|no|on|off)\b"),
], exts=("yml", "yaml"), comment="#")

# ---- Lua ----------------------------------------------------------------------
_lang("Lua", [
    ("comment", r"--\[\[[\s\S]*?(?:\]\]|\Z)"), ("comment", r"--[^\n]*"),
    ("string", r"\[\[[\s\S]*?(?:\]\]|\Z)"), ("string", STR_C),
    ("number", r"\b(?:0[xX][0-9a-fA-F]+|\d+(?:\.\d+)?(?:[eE][+-]?\d+)?)\b"),
    ("keyword", _kw("and break do else elseif end false for function goto if in local nil not "
                    "or repeat return then true until while")),
    ("type", _kw("print pairs ipairs require tostring tonumber type table string math os io "
                 "self setmetatable getmetatable pcall error assert")),
    ("func", FUNC),
], exts=("lua",), comment="--")

PLAIN = "Plain Text"
LANG_NAMES = [PLAIN] + sorted(LANGS, key=str.lower)

EXT_TO_LANG = {}
for _n, _d in LANGS.items():
    for _e in _d["exts"]:
        EXT_TO_LANG[_e] = _n

_REGEX_CACHE = {}


def get_regex(lang):
    """Compile (once) and return the master regex of a language, or None."""
    if lang not in LANGS:
        return None
    rx = _REGEX_CACHE.get(lang)
    if rx is None:
        spec = LANGS[lang]
        parts = ["(?P<%s__%d>%s)" % (tag, i, pat) for i, (tag, pat) in enumerate(spec["rules"])]
        rx = re.compile("|".join(parts), spec["flags"] | re.MULTILINE)
        _REGEX_CACHE[lang] = rx
    return rx


def tokenize(chunk, lang):
    """Yield (tag, start, end) for every token found in *chunk* (pure function)."""
    rx = get_regex(lang)
    if rx is None:
        return
    for m in rx.finditer(chunk):
        s, e = m.span()
        if e > s:
            yield m.lastgroup.split("__")[0], s, e


def detect_language(path, first_line=""):
    ext = os.path.splitext(path or "")[1].lower().lstrip(".")
    if ext in EXT_TO_LANG:
        return EXT_TO_LANG[ext]
    if first_line.startswith("#!"):
        fl = first_line.lower()
        for key, name in (("python", "Python"), ("node", "JavaScript"), ("ruby", "Ruby"),
                          ("lua", "Lua"), ("php", "PHP"), ("bash", "Bash"), ("sh", "Bash")):
            if key in fl:
                return name
    return PLAIN


# =============================================================================
#  THEMES
# =============================================================================
THEMES = {
    "dark": dict(
        bg="#1e1e1e", fg="#d4d4d4", ui_bg="#252526", ui_fg="#cccccc", tab_bg="#2d2d2d",
        gutter_fg="#6e7681", gutter_cur="#c6c6c6", sel="#264f78", cursor="#aeafad",
        found="#6b4a1a", btn="#3a3d41", btn_hover="#4a4d51", scroll="#424242",
        term_bg="#181818", ok="#6a9955", err="#f48771", cmd="#569cd6", dim="#808080",
        comment="#6a9955", string="#ce9178", keyword="#569cd6", type="#4ec9b0",
        number="#b5cea8", func="#dcdcaa", special="#c586c0", attr="#9cdcfe", tag="#569cd6",
        variable="#9cdcfe", heading="#569cd6", bold="#d4d4d4"),
    "light": dict(
        bg="#ffffff", fg="#1f1f1f", ui_bg="#f3f3f3", ui_fg="#333333", tab_bg="#e4e4e4",
        gutter_fg="#999999", gutter_cur="#333333", sel="#add6ff", cursor="#000000",
        found="#ffe08a", btn="#e1e1e1", btn_hover="#d0d0d0", scroll="#c8c8c8",
        term_bg="#fafafa", ok="#008000", err="#c62828", cmd="#0451a5", dim="#777777",
        comment="#008000", string="#a31515", keyword="#0000ff", type="#267f99",
        number="#098658", func="#795e26", special="#af00db", attr="#e50000", tag="#800000",
        variable="#001080", heading="#0000ff", bold="#1f1f1f"),
}


# =============================================================================
#  RUN COMMANDS  (edit build_run_command to add your own languages / compilers)
# =============================================================================
def _q(s):
    return subprocess.list2cmdline([s]) if IS_WIN else shlex.quote(s)


def _oem_encoding():
    """Console code page used by cmd.exe / batch files (output decoding)."""
    if IS_WIN:
        try:
            import ctypes
            enc = "cp%d" % ctypes.windll.kernel32.GetOEMCP()
            codecs.lookup(enc)
            return enc
        except Exception:
            pass
    return "utf-8"


def find_python():
    """Interpreter used to run .py files. A frozen .exe cannot use sys.executable."""
    if not FROZEN:
        exe = sys.executable
        if IS_WIN and exe.lower().endswith("pythonw.exe"):
            cand = os.path.join(os.path.dirname(exe), "python.exe")
            if os.path.exists(cand):
                return [cand]
        return [exe]
    for name, extra in (("py", ["-3"]), ("python", []), ("python3", [])):
        p = shutil.which(name)
        if p:
            return [p] + extra
    return None


def build_run_command(path):
    """Return (command_string, oem_output, error_message). command is None on error."""
    ext = os.path.splitext(path)[1].lower().lstrip(".")
    stem = os.path.splitext(os.path.basename(path))[0]
    exe_suffix = ".exe" if IS_WIN else ""
    out = os.path.join(tempfile.gettempdir(), "goodlite_" + re.sub(r"\W", "_", stem) + exe_suffix)
    f = _q(path)
    o = _q(out)

    if ext in ("py", "pyw"):
        py = find_python()
        if not py:
            return None, False, ("Python was not found on PATH. Install Python 3 from python.org "
                                 "(tick 'Add python.exe to PATH') to run .py files.")
        return " ".join(_q(p) for p in py) + " -u " + f, False, None
    simple = {
        "js": "node %s", "mjs": "node %s", "cjs": "node %s",
        "ts": "npx --yes tsx %s", "rb": "ruby %s", "php": "php %s", "lua": "lua %s",
        "go": "go run %s", "java": "java %s",
        "sh": "bash %s", "bash": "bash %s", "zsh": "zsh %s",
        "ps1": "powershell -NoProfile -ExecutionPolicy Bypass -File %s",
    }
    if ext in simple:
        return simple[ext] % f, False, None
    if ext in ("bat", "cmd"):
        return "cmd /c " + f if IS_WIN else None, True, None if IS_WIN else "Batch files need Windows."
    if ext == "c":
        return "gcc %s -o %s && %s" % (f, o, o), False, None
    if ext in ("cpp", "cc", "cxx"):
        return "g++ -std=c++17 %s -o %s && %s" % (f, o, o), False, None
    if ext == "rs":
        return "rustc %s -o %s && %s" % (f, o, o), False, None
    return None, False, "No run command is defined for '.%s' files (add one in build_run_command)." % ext


# =============================================================================
#  EDITOR TAB
# =============================================================================
class EditorTab(ttk.Frame):
    """One open document: line-number gutter + Text widget + scrollbars."""

    def __init__(self, app, path=None, untitled=None):
        super().__init__(app.notebook)
        
        self.app = app
        self.path = path
        self.untitled = untitled or "Untitled"
        self.dirty = False
        self.eol = "\n"
        self.encoding = "utf-8"
        self.lang = PLAIN
        self._loading = False
        self._hl_job = None
        self._ui_job = None

        self.columnconfigure(1, weight=1)
        self.rowconfigure(0, weight=1)

        self.gutter = tk.Canvas(self, width=44, highlightthickness=0, bd=0)
        self.text = tk.Text(
            self, wrap="word" if app.wrap else "none", undo=True, maxundo=5000,
            font=app.font, bd=0, highlightthickness=0, padx=6, pady=4, insertwidth=2,
            insertofftime=0, exportselection=False)
        self.vbar = ttk.Scrollbar(self, orient="vertical", command=self.text.yview)
        self.hbar = ttk.Scrollbar(self, orient="horizontal", command=self.text.xview)
        self.text.configure(yscrollcommand=self._on_yscroll, xscrollcommand=self.hbar.set)

        self.gutter.grid(row=0, column=0, sticky="ns")
        self.text.grid(row=0, column=1, sticky="nsew")
        self.vbar.grid(row=0, column=2, sticky="ns")
        self.hbar.grid(row=1, column=0, columnspan=2, sticky="ew")

        t = self.text
        t.bind("<<Modified>>", self._on_modified)
        t.bind("<KeyRelease>", self._on_cursor_moved)
        t.bind("<ButtonRelease-1>", self._on_cursor_moved)
        t.bind("<Configure>", lambda e: self._schedule_ui())
        t.bind("<Return>", self._on_return)
        t.bind("<Tab>", lambda e: self._indent(False))
        t.bind("<Shift-Tab>", lambda e: self._indent(True))
        t.bind("<ISO_Left_Tab>", lambda e: self._indent(True))
        t.bind("<Control-a>", self._select_all)
        t.bind("<Control-y>", lambda e: (t.event_generate("<<Redo>>"), "break")[1])
        t.bind("<Control-MouseWheel>", self._on_ctrl_wheel)
        t.bind("<Control-Button-4>", lambda e: (app.zoom(1), "break")[1])
        t.bind("<Control-Button-5>", lambda e: (app.zoom(-1), "break")[1])
        t.bind("<Button-3>", self._context_menu)
        app.bind_shortcuts(t)

        self.apply_theme()
        self.update_tab_stops()

    # ------------------------------------------------------------------ content
    def load(self, raw):
        """Decode *raw* bytes, remember encoding / line endings, fill the widget."""
        try:
            s = raw.decode("utf-8-sig")
            enc = "utf-8-sig" if raw.startswith(codecs.BOM_UTF8) else "utf-8"
        except UnicodeDecodeError:
            try:
                s, enc = raw.decode("cp1252"), "cp1252"
            except UnicodeDecodeError:
                s, enc = raw.decode("latin-1"), "latin-1"
        self.encoding = enc
        self.eol = "\r\n" if "\r\n" in s else ("\r" if "\r" in s else "\n")
        s = s.replace("\r\n", "\n").replace("\r", "\n")
        self._loading = True
        t = self.text
        t.delete("1.0", "end")
        t.insert("1.0", s)
        t.edit_reset()
        t.edit_modified(False)
        t.mark_set("insert", "1.0")
        t.see("1.0")
        self._loading = False
        self.dirty = False
        self.set_language(detect_language(self.path, s.split("\n", 1)[0]))

    def content_bytes(self):
        s = self.text.get("1.0", "end-1c")
        if self.eol != "\n":
            s = s.replace("\n", self.eol)
        try:
            return s.encode(self.encoding)
        except UnicodeEncodeError:
            self.encoding = "utf-8"
            return s.encode("utf-8")

    @property
    def display_name(self):
        return os.path.basename(self.path) if self.path else self.untitled

    # ------------------------------------------------------------------ events
    def _on_modified(self, _e=None):
        t = self.text
        if not t.edit_modified():
            return
        t.edit_modified(False)          # re-arm the event
        if self._loading:
            return
        if not self.dirty:
            self.dirty = True
            self.app.refresh_tab_title(self)
        self.schedule_highlight()
        self._schedule_ui()
        self.app.update_status()

    def _on_cursor_moved(self, _e=None):
        self._schedule_ui()
        self.app.update_status()

    def _on_yscroll(self, first, last):
        self.vbar.set(first, last)
        self._schedule_ui()
        if self._big():
            self.schedule_highlight(60)

    def _on_ctrl_wheel(self, e):
        self.app.zoom(1 if e.delta > 0 else -1)
        return "break"

    def _select_all(self, _e=None):
        self.text.tag_add("sel", "1.0", "end-1c")
        self.text.mark_set("insert", "end-1c")
        return "break"

    def _context_menu(self, e):
        m = tk.Menu(self, tearoff=0)
        for label, ev in (("Cut", "<<Cut>>"), ("Copy", "<<Copy>>"), ("Paste", "<<Paste>>")):
            m.add_command(label=label, command=lambda ev=ev: self.text.event_generate(ev))
        m.add_separator()
        m.add_command(label="Select All", command=self._select_all)
        m.add_command(label="Run File (F5)", command=self.app.run_current)
        m.tk_popup(e.x_root, e.y_root)

    # ------------------------------------------------------------------ editing helpers
    def _on_return(self, _e):
        t = self.text
        if t.tag_ranges("sel"):
            t.delete("sel.first", "sel.last")
        before = t.get("insert linestart", "insert")
        indent = re.match(r"[ \t]*", before).group(0)
        if before.rstrip().endswith((":", "{", "(", "[")):
            indent += "    "
        t.insert("insert", "\n" + indent)
        t.see("insert")
        return "break"

    def _selected_lines(self):
        t = self.text
        if t.tag_ranges("sel"):
            a = int(t.index("sel.first").split(".")[0])
            b_idx = t.index("sel.last")
            b = int(b_idx.split(".")[0])
            if b_idx.endswith(".0") and b > a:
                b -= 1
        else:
            a = b = int(t.index("insert").split(".")[0])
        return a, b

    def _indent(self, dedent):
        t = self.text
        multi = t.tag_ranges("sel") and self._selected_lines()[0] != self._selected_lines()[1]
        if not dedent and not multi:
            if t.tag_ranges("sel"):
                t.delete("sel.first", "sel.last")
            t.insert("insert", "    ")
            return "break"
        a, b = self._selected_lines()
        t.edit_separator()
        for ln in range(a, b + 1):
            if dedent:
                head = t.get("%d.0" % ln, "%d.4" % ln)
                n = len(head) - len(head.lstrip(" "))
                if head.startswith("\t"):
                    n = 1
                if n:
                    t.delete("%d.0" % ln, "%d.%d" % (ln, n))
            else:
                t.insert("%d.0" % ln, "    ")
        t.edit_separator()
        return "break"

    def toggle_comment(self):
        tok = LANGS.get(self.lang, {}).get("comment")
        if not tok:
            self.app.status_message("No line-comment syntax for %s" % self.lang)
            return
        t = self.text
        a, b = self._selected_lines()
        lines = [t.get("%d.0" % n, "%d.end" % n) for n in range(a, b + 1)]
        nonblank = [l for l in lines if l.strip()]
        uncomment = bool(nonblank) and all(l.lstrip().startswith(tok) for l in nonblank)
        t.edit_separator()
        for n, line in zip(range(a, b + 1), lines):
            if not line.strip():
                continue
            ws = len(line) - len(line.lstrip())
            if uncomment:
                cut = len(tok) + (1 if line[ws + len(tok):ws + len(tok) + 1] == " " else 0)
                t.delete("%d.%d" % (n, ws), "%d.%d" % (n, ws + cut))
            else:
                t.insert("%d.%d" % (n, ws), tok + " ")
        t.edit_separator()

    # ------------------------------------------------------------------ language / highlight
    def set_language(self, name):
        self.lang = name if name in LANGS else PLAIN
        self.highlight()
        self.app.update_status()

    def _big(self):
        return int(self.text.index("end-1c").split(".")[0]) > FULL_HL_LINES

    def schedule_highlight(self, delay=90):
        if self._hl_job:
            self.after_cancel(self._hl_job)
        self._hl_job = self.after(delay, self.highlight)

    def highlight(self):
        self._hl_job = None
        t = self.text
        total = int(t.index("end-1c").split(".")[0])
        if total <= FULL_HL_LINES:
            s_line, e_line = 1, total
        else:
            first = int(t.index("@0,0").split(".")[0])
            last = int(t.index("@0,%d" % max(t.winfo_height(), 1)).split(".")[0])
            s_line, e_line = max(1, first - HL_MARGIN), min(total, last + HL_MARGIN)
        a, b = "%d.0" % s_line, "%d.end" % e_line
        for tag in TAGS:
            t.tag_remove(tag, a, b)
        if self.lang not in LANGS:
            return
        chunk = t.get(a, b)
        if len(chunk) > MAX_HL_CHARS:
            return
        starts = [0]
        pos = chunk.find("\n")
        while pos != -1:
            starts.append(pos + 1)
            pos = chunk.find("\n", pos + 1)
        buckets = {}
        for tag, s, e in tokenize(chunk, self.lang):
            l1 = bisect.bisect_right(starts, s) - 1
            l2 = bisect.bisect_right(starts, e) - 1
            buckets.setdefault(tag, []).extend(
                ("%d.%d" % (s_line + l1, s - starts[l1]), "%d.%d" % (s_line + l2, e - starts[l2])))
        for tag, idx in buckets.items():
            for i in range(0, len(idx), 2000):      # keep Tcl argument lists reasonable
                t.tag_add(tag, *idx[i:i + 2000])

    # ------------------------------------------------------------------ gutter
    def _schedule_ui(self):
        if self._ui_job is None:
            self._ui_job = self.after_idle(self._ui_refresh)

    def _ui_refresh(self):
        self._ui_job = None
        try:
            self.redraw_gutter()
        except tk.TclError:
            pass

    def redraw_gutter(self):
        th, t, c, font = self.app.th, self.text, self.gutter, self.app.font
        c.delete("all")
        total = int(t.index("end-1c").split(".")[0])
        width = font.measure("0") * max(3, len(str(total))) + 16
        if int(c.cget("width")) != width:
            c.configure(width=width)
        cur = int(t.index("insert").split(".")[0])
        idx, prev = t.index("@0,0"), None
        while True:
            d = t.dlineinfo(idx)
            if d is None:
                break
            ln = int(idx.split(".")[0])
            if ln != prev:
                c.create_text(width - 8, d[1], anchor="ne", text=str(ln), font=font,
                              fill=th["gutter_cur"] if ln == cur else th["gutter_fg"])
                prev = ln
            nxt = t.index("%s +1 display lines" % idx)
            if nxt == idx:
                break
            idx = nxt

    def update_tab_stops(self):
        self.text.configure(tabs=(self.app.font.measure(" " * 4),))
        self._schedule_ui()

    # ------------------------------------------------------------------ theme
    def apply_theme(self):
        th, t = self.app.th, self.text
        t.configure(bg=th["bg"], fg=th["fg"], insertbackground=th["cursor"],
                    selectbackground=th["sel"], selectforeground=th["fg"],
                    inactiveselectbackground=th["sel"])
        self.gutter.configure(bg=th["bg"])
        for tag in TAGS:
            t.tag_configure(tag, foreground=th[tag])
        t.tag_configure("heading", font=self.app.font_bold)
        t.tag_configure("bold", font=self.app.font_bold)
        t.tag_configure("found", background=th["found"])
        t.tag_raise("found")
        t.tag_raise("sel")
        self._schedule_ui()


# =============================================================================
#  TERMINAL PANEL
# =============================================================================
ANSI_RE = re.compile(r"\x1b\[[0-9;?]*[ -/]*[@-~]|\x1b\][^\x07]*\x07")


class TerminalPanel(ttk.Frame):
    """Output console + input line. Runs processes without any external window."""

    def __init__(self, master, app):
        super().__init__(master)
        self.app = app
        self.proc = None
        self.q = None
        self._poll_job = None
        self._started = 0.0
        self._enc = "utf-8"
        self.cwd = os.path.expanduser("~")
        self.history, self.hist_pos = [], 0


        head = ttk.Frame(self)
        head.pack(fill="x")
        ttk.Label(head, text="  TERMINAL", style="Dim.TLabel").pack(side="left", pady=2)
        ttk.Button(head, text="✕", width=3, command=app.toggle_terminal).pack(side="right", padx=2)
        ttk.Button(head, text="Clear", command=self.clear).pack(side="right", padx=2)
        ttk.Button(head, text="■ Stop", command=self.stop).pack(side="right", padx=2)
        ttk.Button(head, text="▶ Run (F5)", command=app.run_current).pack(side="right", padx=2)

        body = ttk.Frame(self)
        body.pack(fill="both", expand=True)
        body.rowconfigure(0, weight=1)
        body.columnconfigure(0, weight=1)
        self.out = tk.Text(body, height=11, wrap="char", font=app.font, bd=0,
                           highlightthickness=0, padx=8, pady=4, state="disabled",
                           exportselection=False)
        sb = ttk.Scrollbar(body, orient="vertical", command=self.out.yview)
        self.out.configure(yscrollcommand=sb.set)
        self.out.grid(row=0, column=0, sticky="nsew")
        sb.grid(row=0, column=1, sticky="ns")
        self.out.bind("<Button-1>", lambda e: self.out.focus_set())
        self.out.bind("<Button-3>", self._menu)
        self.out.bind("<Control-c>", lambda e: (self.out.event_generate("<<Copy>>"), "break")[1])

        row = ttk.Frame(self)
        row.pack(fill="x")
        self.prompt = ttk.Label(row, text=">", style="Dim.TLabel")
        self.prompt.pack(side="left", padx=(8, 4))
        self.entry = tk.Entry(row, relief="flat", bd=0, highlightthickness=0, font=app.font)
        self.entry.pack(side="left", fill="x", expand=True, pady=3, ipady=2)
        self.entry.bind("<Return>", self._submit)
        self.entry.bind("<Up>", lambda e: self._hist(-1))
        self.entry.bind("<Down>", lambda e: self._hist(1))
        app.bind_shortcuts(self.entry)
        app.bind_shortcuts(self.out)
        self.apply_theme()
        self._update_prompt()

    # ------------------------------------------------------------------ output
    def apply_theme(self):
        th = self.app.th
        self.out.configure(bg=th["term_bg"], fg=th["fg"], selectbackground=th["sel"],
                           selectforeground=th["fg"], inactiveselectbackground=th["sel"])
        self.entry.configure(bg=th["term_bg"], fg=th["fg"], insertbackground=th["cursor"],
                             selectbackground=th["sel"], selectforeground=th["fg"])
        for tag, key in (("cmd", "cmd"), ("ok", "ok"), ("err", "err"), ("dim", "dim")):
            self.out.tag_configure(tag, foreground=th[key])

    def write(self, text, tag=None):
        text = ANSI_RE.sub("", text.replace("\r\n", "\n").replace("\r", "\n"))
        if not text:
            return
        o = self.out
        at_bottom = o.yview()[1] >= 0.999
        o.configure(state="normal")
        o.insert("end", text, tag)
        n = int(o.index("end-1c").split(".")[0])
        if n > TERM_MAX_LINES:
            o.delete("1.0", "%d.0" % (n - TERM_MAX_LINES))
        o.configure(state="disabled")
        if at_bottom:
            o.see("end")

    def clear(self):
        self.out.configure(state="normal")
        self.out.delete("1.0", "end")
        self.out.configure(state="disabled")

    def _menu(self, e):
        m = tk.Menu(self, tearoff=0)
        m.add_command(label="Copy", command=lambda: self.out.event_generate("<<Copy>>"))
        m.add_command(label="Clear", command=self.clear)
        m.tk_popup(e.x_root, e.y_root)

    def _update_prompt(self):
        d = self.cwd
        if len(d) > 38:
            d = "…" + d[-37:]
        self.prompt.configure(text=d + " >")

    # ------------------------------------------------------------------ process control
    def is_running(self):
        return self.proc is not None and self.proc.poll() is None

    def run(self, cmd, cwd, oem=False, echo=None):
        """Start *cmd* (shell string) in *cwd* and stream its output live."""
        self.stop()
        if self._poll_job:
            self.after_cancel(self._poll_job)
            self._poll_job = None
        self.cwd = cwd if os.path.isdir(cwd) else self.cwd
        self._update_prompt()
        self.write("$ %s\n" % (echo or cmd), "cmd")
        env = os.environ.copy()
        env.update(PYTHONUNBUFFERED="1", PYTHONIOENCODING="utf-8", PYTHONUTF8="1")
        kw = dict(shell=True, cwd=self.cwd, stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                  stderr=subprocess.STDOUT, env=env, bufsize=0)
        if IS_WIN:
            kw["creationflags"] = CREATE_NO_WINDOW
        else:
            kw["start_new_session"] = True
        try:
            self.proc = subprocess.Popen(cmd, **kw)
        except Exception as exc:
            self.proc = None
            self.write("Failed to start process: %s\n" % exc, "err")
            return
        self._enc = _oem_encoding() if oem else "utf-8"
        self._started = time.time()
        self.q = queue.Queue()
        threading.Thread(target=self._reader, args=(self.proc, self.q, self._enc),
                         daemon=True).start()
        self._poll()

    @staticmethod
    def _reader(proc, q, enc):
        dec = codecs.getincrementaldecoder(enc)(errors="replace")
        try:
            while True:
                data = proc.stdout.read(4096)       # raw pipe: returns what is available
                if not data:
                    break
                q.put(dec.decode(data))
        except Exception as exc:
            q.put("\n[reader error: %s]\n" % exc)
        try:
            rc = proc.wait()
        except Exception:
            rc = -1
        q.put(("exit", rc))

    def _poll(self):
        self._poll_job = None
        buf, finished, rc, size = [], False, 0, 0
        try:
            while size < 65536:
                item = self.q.get_nowait()
                if isinstance(item, tuple):
                    finished, rc = True, item[1]
                    break
                size += len(item)
                buf.append(item)
        except queue.Empty:
            pass
        if buf:
            self.write("".join(buf))
        if finished:
            self.write("\n[Process finished with exit code %s in %.2fs]\n"
                       % (rc, time.time() - self._started), "ok" if rc == 0 else "err")
            self.proc = None
        else:
            self._poll_job = self.after(30, self._poll)

    def stop(self):
        p = self.proc
        if p is None or p.poll() is not None:
            return
        try:
            if IS_WIN:
                subprocess.run(["taskkill", "/F", "/T", "/PID", str(p.pid)],
                               stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL,
                               creationflags=CREATE_NO_WINDOW)
            else:
                os.killpg(os.getpgid(p.pid), signal.SIGKILL)
        except Exception:
            try:
                p.kill()
            except Exception:
                pass
        self.write("\n[Stopped]\n", "dim")

    # ------------------------------------------------------------------ input line
    def _hist(self, step):
        if not self.history:
            return "break"
        self.hist_pos = max(0, min(len(self.history), self.hist_pos + step))
        self.entry.delete(0, "end")
        if self.hist_pos < len(self.history):
            self.entry.insert(0, self.history[self.hist_pos])
        return "break"

    def _submit(self, _e=None):
        line = self.entry.get()
        self.entry.delete(0, "end")
        if self.is_running():                       # forward to the program's stdin
            self.write(line + "\n", "cmd")
            try:
                self.proc.stdin.write((line + "\n").encode(self._enc, errors="replace"))
                self.proc.stdin.flush()
            except Exception as exc:
                self.write("[could not write to process: %s]\n" % exc, "err")
            return
        line = line.strip()
        if not line:
            return
        self.history.append(line)
        self.hist_pos = len(self.history)
        low = line.lower()
        if low in ("cls", "clear"):
            self.clear()
            return
        m = re.match(r"^cd(?:\s+/d)?(?:\s+(.*))?$", line, re.I)
        if m and "&&" not in line:
            target = (m.group(1) or "").strip().strip('"')
            if not target:
                self.write(self.cwd + "\n")
            else:
                new = os.path.normpath(os.path.join(self.cwd, os.path.expanduser(target)))
                if os.path.isdir(new):
                    self.cwd = new
                    self._update_prompt()
                else:
                    self.write("The system cannot find the path specified: %s\n" % target, "err")
            return
        self.run(line, self.cwd, oem=True)


# =============================================================================
#  MAIN APPLICATION
# =============================================================================
class App:
    def __init__(self, files):
        self.root = tk.Tk()
        self.root.title(APP_NAME)
        self.root.geometry("1100x720")
        # --- ICON SETUP ---
        try:
            icon_path = os.path.join(os.path.dirname(__file__), "icon.ico")
            if os.path.exists(icon_path):
                self.root.iconbitmap(icon_path)
        except Exception:
            pass
        # ------------------
        self.root.minsize(640, 400)
        self.root.report_callback_exception = self._on_exception

        self.dark = True
        self.wrap = False
        self.th = THEMES["dark"]
        self.untitled_n = 0
        families = set(tkfont.families(self.root))
        fam = next((f for f in ("Consolas", "Cascadia Mono", "DejaVu Sans Mono", "Menlo",
                                "Courier New") if f in families), "TkFixedFont")
        self.font = tkfont.Font(family=fam, size=11)
        self.font_bold = tkfont.Font(family=fam, size=11, weight="bold")

        self.style = ttk.Style(self.root)
        self.style.theme_use("clam")

        self._build_shortcuts()
        self._build_ui()
        self.apply_theme()

        opened = False
        for f in files:
            if os.path.isfile(f):
                self.open_path(os.path.abspath(f))
                opened = True
        if not opened:
            self.new_file()
        self.terminal.write("%s ready.  F5 = run current file,  Shift+F5 = stop,  "
                            "Ctrl+` = show/hide terminal.\n" % APP_NAME, "dim")
        self.root.protocol("WM_DELETE_WINDOW", self.on_exit)
    def stop_run(self):
        self.terminal.stop()

    # ------------------------------------------------------------------ construction
    def _build_shortcuts(self):
        self.shortcuts = {
            "<Control-n>": self.new_file, "<Control-o>": self.open_files,
            "<Control-s>": self.save_current, "<Control-Shift-S>": self.save_as_current,
            "<Control-w>": self.close_current, "<Control-q>": self.on_exit,
            "<F5>": self.run_current, "<Shift-F5>": self.stop_run,
            "<Control-f>": self.show_find, "<Control-h>": lambda: self.show_find(True),
            "<Control-g>": self.goto_line, "<Control-slash>": self.toggle_comment,
            "<Control-grave>": self.toggle_terminal, "<Control-Shift-D>": self.toggle_theme,
            "<Control-equal>": lambda: self.zoom(1), "<Control-plus>": lambda: self.zoom(1),
            "<Control-KP_Add>": lambda: self.zoom(1), "<Control-minus>": lambda: self.zoom(-1),
            "<Control-KP_Subtract>": lambda: self.zoom(-1), "<Control-0>": lambda: self.zoom(0),
        }

    def bind_shortcuts(self, widget):
        """Bind every global shortcut on *widget* and stop Tk's built-in emacs bindings."""
        for seq, fn in self.shortcuts.items():
            widget.bind(seq, lambda e, f=fn: (f(), "break")[1])

    def _build_ui(self):
        root = self.root
        # status bar (packed first so it stays at the very bottom)
        self.statusbar = ttk.Frame(root)
        self.statusbar.pack(side="bottom", fill="x")
        self.st_pos = ttk.Label(self.statusbar, text="Ln 1, Col 1", style="Status.TLabel")
        self.st_msg = ttk.Label(self.statusbar, text="", style="Status.TLabel")
        self.st_lang = ttk.Label(self.statusbar, text=PLAIN, style="Status.TLabel")
        self.st_enc = ttk.Label(self.statusbar, text="UTF-8", style="Status.TLabel")
        self.st_pos.pack(side="left", padx=10)
        self.st_msg.pack(side="left", padx=10)
        for w in (self.st_enc, self.st_lang):
            w.pack(side="right", padx=10)

        self.paned = ttk.PanedWindow(root, orient="vertical")
        self.paned.pack(fill="both", expand=True)
        self.notebook = ttk.Notebook(self.paned)
        self.notebook.bind("<<NotebookTabChanged>>", self._on_tab_changed)
        self.notebook.bind("<ButtonRelease-2>", self._on_tab_middle_click)
        self.notebook.bind("<Button-3>", self._on_tab_right_click)
        self.paned.add(self.notebook, weight=4)
        self.terminal = TerminalPanel(self.paned, self)
        self.paned.add(self.terminal, weight=1)
        self.terminal_visible = True

        self._build_findbar()
        self._build_menu()
        self.bind_shortcuts(root)

    def _build_menu(self):
        root = self.root
        bar = tk.Menu(root)
        self.menubar = bar

        m = tk.Menu(bar, tearoff=0)
        m.add_command(label="New File", accelerator="Ctrl+N", command=self.new_file)
        m.add_command(label="Open…", accelerator="Ctrl+O", command=self.open_files)
        m.add_command(label="Save", accelerator="Ctrl+S", command=self.save_current)
        m.add_command(label="Save As…", accelerator="Ctrl+Shift+S", command=self.save_as_current)
        m.add_separator()
        m.add_command(label="Close Tab", accelerator="Ctrl+W", command=self.close_current)
        m.add_command(label="Exit", accelerator="Ctrl+Q", command=self.on_exit)
        bar.add_cascade(label="File", menu=m)

        m = tk.Menu(bar, tearoff=0)
        for label, ev, acc in (("Undo", "<<Undo>>", "Ctrl+Z"), ("Redo", "<<Redo>>", "Ctrl+Y"),
                               (None, None, None), ("Cut", "<<Cut>>", "Ctrl+X"),
                               ("Copy", "<<Copy>>", "Ctrl+C"), ("Paste", "<<Paste>>", "Ctrl+V")):
            if label is None:
                m.add_separator()
            else:
                m.add_command(label=label, accelerator=acc,
                              command=lambda ev=ev: self._text_event(ev))
        m.add_command(label="Select All", accelerator="Ctrl+A", command=self._select_all)
        m.add_separator()
        m.add_command(label="Find / Replace…", accelerator="Ctrl+F", command=self.show_find)
        m.add_command(label="Go to Line…", accelerator="Ctrl+G", command=self.goto_line)
        m.add_command(label="Toggle Line Comment", accelerator="Ctrl+/", command=self.toggle_comment)
        bar.add_cascade(label="Edit", menu=m)

        m = tk.Menu(bar, tearoff=0)
        m.add_command(label="Run Current File", accelerator="F5", command=self.run_current)
        m.add_command(label="Stop", accelerator="Shift+F5", command=self.stop_run)
        bar.add_cascade(label="Run", menu=m)

        self.lang_var = tk.StringVar(value=PLAIN)
        lm = tk.Menu(bar, tearoff=0)
        for name in LANG_NAMES:
            lm.add_radiobutton(label=name, value=name, variable=self.lang_var,
                               command=lambda n=name: self._set_lang(n))
        bar.add_cascade(label="Language", menu=lm)

        m = tk.Menu(bar, tearoff=0)
        m.add_command(label="Toggle Terminal", accelerator="Ctrl+`", command=self.toggle_terminal)
        m.add_command(label="Toggle Dark / Light", accelerator="Ctrl+Shift+D",
                      command=self.toggle_theme)
        self.wrap_var = tk.BooleanVar(value=False)
        m.add_checkbutton(label="Word Wrap", variable=self.wrap_var, command=self.toggle_wrap)
        m.add_separator()
        m.add_command(label="Zoom In", accelerator="Ctrl++", command=lambda: self.zoom(1))
        m.add_command(label="Zoom Out", accelerator="Ctrl+-", command=lambda: self.zoom(-1))
        m.add_command(label="Reset Zoom", accelerator="Ctrl+0", command=lambda: self.zoom(0))
        bar.add_cascade(label="View", menu=m)
        root.configure(menu=bar)

    def _build_findbar(self):
        fb = ttk.Frame(self.root)
        self.findbar = fb
        self.find_var, self.repl_var = tk.StringVar(), tk.StringVar()
        self.case_var = tk.BooleanVar(value=False)
        ttk.Label(fb, text=" Find").grid(row=0, column=0, padx=(6, 2), pady=2)
        self.find_entry = tk.Entry(fb, textvariable=self.find_var, width=30, relief="flat")
        self.find_entry.grid(row=0, column=1, padx=2, ipady=2)
        ttk.Button(fb, text="Prev", command=lambda: self.find_next(True)).grid(row=0, column=2, padx=2)
        ttk.Button(fb, text="Next", command=self.find_next).grid(row=0, column=3, padx=2)
        ttk.Checkbutton(fb, text="Match case", variable=self.case_var,
                        command=self._find_highlight_all).grid(row=0, column=4, padx=6)
        self.find_count = ttk.Label(fb, text="", style="Dim.TLabel")
        self.find_count.grid(row=0, column=5, padx=4)
        ttk.Button(fb, text="✕", width=3, command=self.hide_find).grid(row=0, column=6, padx=4)
        ttk.Label(fb, text=" Replace").grid(row=1, column=0, padx=(6, 2), pady=2)
        self.repl_entry = tk.Entry(fb, textvariable=self.repl_var, width=30, relief="flat")
        self.repl_entry.grid(row=1, column=1, padx=2, ipady=2)
        ttk.Button(fb, text="Replace", command=self.replace_one).grid(row=1, column=2, padx=2)
        ttk.Button(fb, text="All", command=self.replace_all).grid(row=1, column=3, padx=2)
        for e in (self.find_entry, self.repl_entry):
            e.bind("<Escape>", lambda ev: self.hide_find())
        self.find_entry.bind("<Return>", lambda ev: self.find_next())
        self.find_entry.bind("<Shift-Return>", lambda ev: self.find_next(True))
        self.find_var.trace_add("write", lambda *a: self._find_highlight_all())

    # ------------------------------------------------------------------ theme
    def apply_theme(self):
        th = self.th = THEMES["dark" if self.dark else "light"]
        st = self.style
        st.configure(".", background=th["ui_bg"], foreground=th["ui_fg"],
                     fieldbackground=th["bg"], borderwidth=0, focuscolor=th["ui_bg"])
        st.configure("TFrame", background=th["ui_bg"])
        st.configure("TLabel", background=th["ui_bg"], foreground=th["ui_fg"])
        st.configure("Dim.TLabel", background=th["ui_bg"], foreground=th["dim"])
        st.configure("Status.TLabel", background=th["ui_bg"], foreground=th["ui_fg"], padding=(0, 2))
        st.configure("TNotebook", background=th["ui_bg"], borderwidth=0, tabmargins=(2, 4, 2, 0))
        st.configure("TNotebook.Tab", background=th["tab_bg"], foreground=th["ui_fg"],
                     padding=(14, 5), borderwidth=0)
        st.map("TNotebook.Tab", background=[("selected", th["bg"])],
               foreground=[("selected", th["fg"])])
        st.configure("TButton", background=th["btn"], foreground=th["ui_fg"], padding=(8, 1),
                     borderwidth=0, relief="flat")
        st.map("TButton", background=[("active", th["btn_hover"])])
        st.configure("TCheckbutton", background=th["ui_bg"], foreground=th["ui_fg"])
        st.map("TCheckbutton", background=[("active", th["ui_bg"])])
        for orient in ("Vertical", "Horizontal"):
            st.configure(orient + ".TScrollbar", background=th["scroll"], troughcolor=th["bg"],
                         bordercolor=th["bg"], lightcolor=th["scroll"], darkcolor=th["scroll"],
                         arrowcolor=th["ui_fg"])
        self.root.configure(bg=th["ui_bg"])
        for e in (self.find_entry, self.repl_entry):
            e.configure(bg=th["bg"], fg=th["fg"], insertbackground=th["cursor"],
                        selectbackground=th["sel"], selectforeground=th["fg"])
        self.terminal.apply_theme()
        for tab in self.tabs():
            tab.apply_theme()

    def toggle_theme(self):
        self.dark = not self.dark
        self.apply_theme()

    def toggle_wrap(self):
        self.wrap = self.wrap_var.get()
        for tab in self.tabs():
            tab.text.configure(wrap="word" if self.wrap else "none")
            tab._schedule_ui()

    def zoom(self, delta):
        size = 11 if delta == 0 else max(7, min(40, self.font.cget("size") + delta))
        self.font.configure(size=size)
        self.font_bold.configure(size=size)
        for tab in self.tabs():
            tab.update_tab_stops()

    # ------------------------------------------------------------------ tab helpers
    def tabs(self):
        return [self.notebook.nametowidget(t) for t in self.notebook.tabs()]

    def current_tab(self):
        sel = self.notebook.select()
        return self.notebook.nametowidget(sel) if sel else None

    def _on_tab_changed(self, _e=None):
        tab = self.current_tab()
        if tab:
            tab.text.focus_set()
            tab._schedule_ui()
            if tab._big():
                tab.schedule_highlight(30)
            self.lang_var.set(tab.lang)
        self.update_status()
        self._update_title()

    def _on_tab_middle_click(self, e):
        try:
            idx = self.notebook.index("@%d,%d" % (e.x, e.y))
        except tk.TclError:
            return
        self.close_tab(self.tabs()[idx])

    def _on_tab_right_click(self, e):
        try:
            idx = self.notebook.index("@%d,%d" % (e.x, e.y))
        except tk.TclError:
            return
        tab = self.tabs()[idx]
        m = tk.Menu(self.root, tearoff=0)
        m.add_command(label="Close", command=lambda: self.close_tab(tab))
        m.add_command(label="Close Others", command=lambda: self._close_others(tab))
        if tab.path:
            m.add_command(label="Copy Path", command=lambda: (
                self.root.clipboard_clear(), self.root.clipboard_append(tab.path)))
        m.tk_popup(e.x_root, e.y_root)

    def _close_others(self, keep):
        for t in self.tabs():
            if t is not keep and not self.close_tab(t):
                break

    def refresh_tab_title(self, tab):
        try:
            self.notebook.tab(tab, text=tab.display_name + (" ●" if tab.dirty else ""))
        except tk.TclError:
            return
        if tab is self.current_tab():
            self._update_title()

    def _update_title(self):
        tab = self.current_tab()
        if tab:
            self.root.title("%s%s — %s" % (tab.path or tab.untitled,
                                           " ●" if tab.dirty else "", APP_NAME))
        else:
            self.root.title(APP_NAME)

    def update_status(self):
        tab = self.current_tab()
        if not tab:
            return
        try:
            ln, col = tab.text.index("insert").split(".")
            self.st_pos.configure(text="Ln %s, Col %d" % (ln, int(col) + 1))
        except tk.TclError:
            return
        self.st_lang.configure(text=tab.lang)
        self.st_enc.configure(text="%s  %s" % (tab.encoding.upper().replace("-SIG", " BOM"),
                                               {"\n": "LF", "\r\n": "CRLF", "\r": "CR"}[tab.eol]))
        self.lang_var.set(tab.lang)

    def status_message(self, msg):
        self.st_msg.configure(text=msg)
        self.root.after(4000, lambda: self.st_msg.configure(text=""))

    def _set_lang(self, name):
        tab = self.current_tab()
        if tab:
            tab.set_language(name)

    # ------------------------------------------------------------------ file operations
    def new_file(self):
        self.untitled_n += 1
        tab = EditorTab(self, untitled="Untitled-%d" % self.untitled_n)
        self.notebook.add(tab, text=tab.display_name)
        self.notebook.select(tab)
        return tab

    def open_files(self):
        paths = filedialog.askopenfilenames(parent=self.root, title="Open file(s)",
                                            filetypes=[("All files", "*.*")])
        for p in paths:
            self.open_path(p)

    def open_path(self, path):
        path = os.path.abspath(path)
        for t in self.tabs():                       # already open -> just switch to it
            if t.path and os.path.normcase(t.path) == os.path.normcase(path):
                self.notebook.select(t)
                return t
        try:
            size = os.path.getsize(path)
            if size > BIG_FILE_BYTES and not messagebox.askyesno(
                    APP_NAME, "This file is %.1f MB. Large files can be slow to edit.\n\n"
                              "Open anyway?" % (size / 1048576), parent=self.root):
                return None
            with open(path, "rb") as f:
                raw = f.read()
        except Exception as exc:
            messagebox.showerror(APP_NAME, "Cannot open file:\n%s\n\n%s" % (path, exc),
                                 parent=self.root)
            return None
        # re-use a pristine empty "Untitled" tab
        cur = self.current_tab()
        if cur and cur.path is None and not cur.dirty and cur.text.get("1.0", "end-1c") == "":
            self._remove_tab(cur)
        tab = EditorTab(self, path=path)
        tab.load(raw)
        self.notebook.add(tab, text=tab.display_name)
        self.notebook.select(tab)
        self.terminal.cwd = os.path.dirname(path)
        self.terminal._update_prompt()
        return tab

    def save_tab(self, tab, save_as=False):
        path = tab.path
        if path is None or save_as:
            init = os.path.dirname(path) if path else self.terminal.cwd
            path = filedialog.asksaveasfilename(
                parent=self.root, title="Save As", initialdir=init,
                initialfile=tab.display_name, filetypes=[("All files", "*.*")])
            if not path:
                return False
        try:
            data = tab.content_bytes()
            with open(path, "wb") as f:
                f.write(data)
        except Exception as exc:
            messagebox.showerror(APP_NAME, "Cannot save file:\n%s\n\n%s" % (path, exc),
                                 parent=self.root)
            return False
        changed = path != tab.path
        tab.path = os.path.abspath(path)
        tab.dirty = False
        if changed:
            tab.set_language(detect_language(tab.path, tab.text.get("1.0", "1.end")))
        self.refresh_tab_title(tab)
        self.update_status()
        self.status_message("Saved %s" % tab.display_name)
        return True

    def save_current(self):
        tab = self.current_tab()
        return self.save_tab(tab) if tab else False

    def save_as_current(self):
        tab = self.current_tab()
        return self.save_tab(tab, save_as=True) if tab else False

    def _remove_tab(self, tab):
        self.notebook.forget(tab)
        tab.destroy()

    def close_tab(self, tab):
        """Close *tab* (asking about unsaved changes). Returns False if cancelled."""
        if tab.dirty:
            self.notebook.select(tab)
            ans = messagebox.askyesnocancel(
                APP_NAME, "Save changes to %s before closing?" % tab.display_name,
                parent=self.root)
            if ans is None or (ans and not self.save_tab(tab)):
                return False
        self._remove_tab(tab)
        if not self.tabs():
            self.new_file()
        return True

    def close_current(self):
        tab = self.current_tab()
        if tab:
            self.close_tab(tab)

    def on_exit(self):
        for tab in self.tabs():
            if not self.close_tab(tab):
                return
        self.terminal.stop()
        self.root.destroy()

    # ------------------------------------------------------------------ edit commands
    def _text_event(self, ev):
        tab = self.current_tab()
        if tab:
            tab.text.focus_set()
            tab.text.event_generate(ev)

    def _select_all(self):
        tab = self.current_tab()
        if tab:
            tab._select_all()

    def toggle_comment(self):
        tab = self.current_tab()
        if tab:
            tab.toggle_comment()

    def goto_line(self):
        tab = self.current_tab()
        if not tab:
            return
        total = int(tab.text.index("end-1c").split(".")[0])
        n = simpledialog.askinteger("Go to line", "Line number (1-%d):" % total, parent=self.root,
                                    minvalue=1, maxvalue=total)
        if n:
            tab.text.mark_set("insert", "%d.0" % n)
            tab.text.see("insert")
            tab.text.focus_set()
            self.update_status()

    # ------------------------------------------------------------------ find / replace
    def show_find(self, replace=False):
        if not self.findbar.winfo_ismapped():
            self.findbar.pack(side="bottom", fill="x", before=self.paned)
        tab = self.current_tab()
        if tab and tab.text.tag_ranges("sel"):
            sel = tab.text.get("sel.first", "sel.last")
            if "\n" not in sel:
                self.find_var.set(sel)
        (self.repl_entry if replace else self.find_entry).focus_set()
        self.find_entry.select_range(0, "end")
        self._find_highlight_all()

    def hide_find(self):
        for tab in self.tabs():
            tab.text.tag_remove("found", "1.0", "end")
        self.findbar.pack_forget()
        tab = self.current_tab()
        if tab:
            tab.text.focus_set()

    def _search(self, tab, start, stop=None, backwards=False):
        pat = self.find_var.get()
        if not pat:
            return None, 0
        cnt = tk.IntVar()
        idx = tab.text.search(pat, start, stopindex=stop, nocase=not self.case_var.get(),
                              backwards=backwards, count=cnt)
        return (idx or None), cnt.get()

    def _find_highlight_all(self):
        tab = self.current_tab()
        if not tab or not self.findbar.winfo_ismapped():
            return
        t = tab.text
        t.tag_remove("found", "1.0", "end")
        pat, n, idx = self.find_var.get(), 0, "1.0"
        if not pat:
            self.find_count.configure(text="")
            return
        while n < 5000:
            idx, length = self._search(tab, idx, "end")
            if not idx or length == 0:
                break
            end = "%s+%dc" % (idx, length)
            t.tag_add("found", idx, end)
            idx, n = end, n + 1
        self.find_count.configure(text="%d match%s" % (n, "" if n == 1 else "es") if n < 5000
                                  else "5000+ matches")

    def find_next(self, backwards=False):
        tab = self.current_tab()
        if not tab or not self.find_var.get():
            return
        t = tab.text
        if backwards:
            start = t.index("sel.first") if t.tag_ranges("sel") else t.index("insert")
            idx, length = self._search(tab, start, "1.0", backwards=True)
            if not idx:
                idx, length = self._search(tab, "end", start, backwards=True)
        else:
            start = t.index("sel.last") if t.tag_ranges("sel") else t.index("insert")
            idx, length = self._search(tab, start, "end")
            if not idx:
                idx, length = self._search(tab, "1.0", start)
        if not idx:
            self.status_message("Not found")
            return
        t.tag_remove("sel", "1.0", "end")
        t.tag_add("sel", idx, "%s+%dc" % (idx, length))
        t.mark_set("insert", idx if backwards else "%s+%dc" % (idx, length))
        t.see(idx)

    def replace_one(self):
        tab = self.current_tab()
        if not tab:
            return
        t = tab.text
        if t.tag_ranges("sel"):
            sel = t.get("sel.first", "sel.last")
            pat = self.find_var.get()
            if sel == pat or (not self.case_var.get() and sel.lower() == pat.lower()):
                t.edit_separator()
                t.delete("sel.first", "sel.last")
                t.insert("insert", self.repl_var.get())
                t.edit_separator()
        self.find_next()

    def replace_all(self):
        tab = self.current_tab()
        if not tab or not self.find_var.get():
            return
        t, n, idx = tab.text, 0, "1.0"
        repl = self.repl_var.get()
        t.edit_separator()
        while True:
            idx, length = self._search(tab, idx, "end")
            if not idx or length == 0:
                break
            t.delete(idx, "%s+%dc" % (idx, length))
            t.insert(idx, repl)
            idx = "%s+%dc" % (idx, len(repl))
            n += 1
        t.edit_separator()
        self._find_highlight_all()
        self.status_message("Replaced %d occurrence%s" % (n, "" if n == 1 else "s"))

    # ------------------------------------------------------------------ run / terminal
    def toggle_terminal(self):
        if self.terminal_visible:
            self.paned.forget(self.terminal)
        else:
            self.paned.add(self.terminal, weight=1)
        self.terminal_visible = not self.terminal_visible
        tab = self.current_tab()
        if tab:
            tab.text.focus_set()

    def _show_terminal(self):
        if not self.terminal_visible:
            self.toggle_terminal()

    def run_current(self):
        tab = self.current_tab()
        if not tab:
            return
        if tab.path is None or tab.dirty:          # auto-save before running
            if not self.save_tab(tab):
                return
        
        # --- SAFETY CHECK / CONSENT SYSTEM ---
        try:
            with open(tab.path, "r", encoding="utf-8", errors="ignore") as f:
                code_content = f.read()
            
            # Dangerous keywords check jo system ko nuksan de sakte hain
            dangerous_patterns = ["os.remove", "shutil.rmtree", "os.rmdir", "subprocess", "eval(", "exec("]
            found_risks = [p for p in dangerous_patterns if p in code_content]
            
            if found_risks:
                warning_msg = (
                    "⚠️ Security Warning!\n\n"
                    f"This code contains potentially risky operations: {', '.join(found_risks)}\n"
                    "This code might harm your device.\n\n"
                    "Do you still want to run it?"
                )
                if not messagebox.askyesno(APP_NAME, warning_msg, parent=self.root):
                    self.terminal.write("[Run cancelled by user due to security warning]\n", "err")
                    return
        except Exception:
            pass
        # -------------------------------------

        self._show_terminal()
        ext = os.path.splitext(tab.path)[1].lower()
        if ext in (".html", ".htm"):
            self.terminal.write("Opening %s in your default browser…\n" % tab.display_name, "cmd")
            webbrowser.open("file:///" + tab.path.replace("\\", "/").lstrip("/"))
            return
        cmd, oem, err = build_run_command(tab.path)
        if not cmd:
            self.terminal.write("%s\n" % err, "err")
            return
        self.terminal.run(cmd, os.path.dirname(tab.path), oem=oem)

    # ------------------------------------------------------------------ misc
    def _on_exception(self, exc, val, tb):
        text = "".join(traceback.format_exception(exc, val, tb))
        try:
            self.terminal.write("[internal error]\n" + text + "\n", "err")
        except Exception:
            pass

    def run_app(self):
        self.root.mainloop()


def main():
    if IS_WIN:                                      # crisp text on high-DPI displays
        try:
            import ctypes
            ctypes.windll.shcore.SetProcessDpiAwareness(1)
        except Exception:
            pass
    App(sys.argv[1:]).run_app()


if __name__ == "__main__":
    main()