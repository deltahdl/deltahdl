#include "preprocessor/preprocessor.h"

#include <algorithm>
#include <cctype>
#include <fstream>
#include <sstream>

namespace delta {

Preprocessor::Preprocessor(SourceManager& src_mgr, DiagEngine& diag,
                           PreprocConfig config)
    : src_mgr_(src_mgr), diag_(diag), config_(std::move(config)) {
  for (const auto& [name, value] : config_.defines) {
    MacroDef def;
    def.name = name;
    def.body = value;
    macros_.Define(std::move(def));
  }
}

std::string Preprocessor::Preprocess(uint32_t file_id) {
  auto content = src_mgr_.FileContent(file_id);
  return ProcessSource(content, file_id, 0);
}

static std::string_view Trim(std::string_view s) {
  while (!s.empty() && std::isspace(static_cast<unsigned char>(s.front()))) {
    s.remove_prefix(1);
  }
  while (!s.empty() && std::isspace(static_cast<unsigned char>(s.back()))) {
    s.remove_suffix(1);
  }
  return s;
}

static bool StartsWithDirective(std::string_view line, std::string_view dir) {
  auto trimmed = Trim(line);
  if (trimmed.size() < dir.size() + 1) {
    return false;
  }
  if (trimmed[0] != '`') {
    return false;
  }
  return trimmed.substr(1, dir.size()) == dir;
}

static std::string_view AfterDirective(std::string_view line,
                                       std::string_view dir) {
  auto trimmed = Trim(line);
  auto rest = trimmed.substr(1 + dir.size());
  return Trim(rest);
}

std::string Preprocessor::ProcessSource(std::string_view src, uint32_t file_id,
                                        int depth) {
  if (depth > kMaxIncludeDepth) {
    diag_.Error({file_id, 1, 1}, "include depth exceeds maximum of 15");
    return "";
  }

  std::string output;
  output.reserve(src.size());
  uint32_t line_num = 0;
  size_t pos = 0;

  while (pos < src.size()) {
    size_t eol = src.find('\n', pos);
    if (eol == std::string_view::npos) {
      eol = src.size();
    }
    std::string_view line = src.substr(pos, eol - pos);
    ++line_num;

    bool handled = ProcessDirective(line, file_id, line_num, depth, output);
    if (!handled && IsActive()) {
      output.append(line);
    }
    output.push_back('\n');
    pos = eol + 1;
  }
  return output;
}

bool Preprocessor::ProcessDirective(std::string_view line, uint32_t file_id,
                                    uint32_t line_num, int depth,
                                    std::string& output) {
  auto trimmed = Trim(line);
  if (trimmed.empty()) return false;
  if (trimmed[0] != '`') return false;
  SourceLoc loc = {file_id, line_num, 1};

  if (StartsWithDirective(line, "define")) {
    HandleDefine(AfterDirective(line, "define"), loc);
    return true;
  }
  if (StartsWithDirective(line, "undef")) {
    HandleUndef(AfterDirective(line, "undef"), loc);
    return true;
  }
  if (ProcessConditionalDirective(line)) return true;
  if (StartsWithDirective(line, "include") && IsActive()) {
    HandleInclude(AfterDirective(line, "include"), loc, depth, output);
    return true;
  }
  if (StartsWithDirective(line, "timescale")) {
    return true;  // consumed, handled later
  }
  if (StartsWithDirective(line, "resetall")) {
    macros_.UndefineAll();
    return true;
  }
  // Check for macro invocation: `MACRO_NAME
  if (IsActive() && TryExpandMacro(trimmed, output, file_id, line_num)) {
    return true;
  }
  return false;
}

bool Preprocessor::ProcessConditionalDirective(std::string_view line) {
  if (StartsWithDirective(line, "ifdef")) {
    HandleIfdef(AfterDirective(line, "ifdef"), false);
    return true;
  }
  if (StartsWithDirective(line, "ifndef")) {
    HandleIfdef(AfterDirective(line, "ifndef"), true);
    return true;
  }
  if (StartsWithDirective(line, "elsif")) {
    HandleElsif(AfterDirective(line, "elsif"));
    return true;
  }
  if (StartsWithDirective(line, "else")) {
    HandleElse();
    return true;
  }
  if (StartsWithDirective(line, "endif")) {
    HandleEndif();
    return true;
  }
  return false;
}

bool Preprocessor::TryExpandMacro(std::string_view trimmed, std::string& output,
                                  uint32_t file_id, uint32_t line_num) {
  auto macro_name = trimmed.substr(1);
  auto space_pos = macro_name.find_first_of(" \t(");
  auto name = (space_pos != std::string_view::npos)
                  ? macro_name.substr(0, space_pos)
                  : macro_name;

  // Predefined macros (IEEE 1800-2023 §22.13).
  if (name == "__FILE__") {
    output.append("\"");
    output.append(src_mgr_.FilePath(file_id));
    output.append("\"");
    return true;
  }
  if (name == "__LINE__") {
    output.append(std::to_string(line_num));
    return true;
  }

  const auto* def = macros_.Lookup(name);
  if (def == nullptr) return false;

  std::string_view args_text;
  if (def->is_function_like) {
    auto after_name = macro_name.substr(name.size());
    auto balanced = ExtractBalancedArgs(after_name);
    if (balanced.empty()) return false;
    args_text = balanced.substr(1, balanced.size() - 2);
  }
  output.append(ExpandMacro(*def, args_text));
  return true;
}

bool Preprocessor::IsActive() const {
  return std::all_of(cond_stack_.begin(), cond_stack_.end(),
                     [](const CondState& s) { return s.active; });
}

static bool IsIdentChar(char c) {
  return std::isalnum(static_cast<unsigned char>(c)) || c == '_';
}

void Preprocessor::HandleDefine(std::string_view rest, SourceLoc loc) {
  if (!IsActive()) return;

  // Find where the macro name ends.
  size_t name_end = 0;
  while (name_end < rest.size() && IsIdentChar(rest[name_end])) ++name_end;

  MacroDef def;
  def.def_loc = loc;
  if (name_end == 0) return;

  def.name = std::string(rest.substr(0, name_end));
  auto after_name = rest.substr(name_end);

  // Function-like: `( immediately after name, NO space (IEEE §22.5.1).
  if (!after_name.empty() && after_name[0] == '(') {
    auto close = after_name.find(')');
    if (close != std::string_view::npos) {
      def.is_function_like = true;
      def.params = ParseMacroParams(after_name.substr(1, close - 1));
      def.body = std::string(Trim(after_name.substr(close + 1)));
    }
  } else {
    def.body = std::string(Trim(after_name));
  }
  macros_.Define(std::move(def));
}

void Preprocessor::HandleUndef(std::string_view rest, SourceLoc /*loc*/) {
  if (!IsActive()) return;
  auto name = Trim(rest);
  macros_.Undefine(name);
}

void Preprocessor::HandleIfdef(std::string_view rest, bool inverted) {
  auto name = Trim(rest);
  bool defined = macros_.IsDefined(name);
  bool cond = inverted ? !defined : defined;
  bool parent = IsActive();
  bool active = parent && cond;
  cond_stack_.push_back({active, active, parent});
}

void Preprocessor::HandleElsif(std::string_view rest) {
  if (cond_stack_.empty()) return;
  auto& top = cond_stack_.back();
  auto name = Trim(rest);
  bool defined = macros_.IsDefined(name);
  top.active = top.parent_active && !top.any_taken && defined;
  if (top.active) top.any_taken = true;
}

void Preprocessor::HandleElse() {
  if (cond_stack_.empty()) return;
  auto& top = cond_stack_.back();
  top.active = top.parent_active && !top.any_taken;
  top.any_taken = true;
}

void Preprocessor::HandleEndif() {
  if (!cond_stack_.empty()) {
    cond_stack_.pop_back();
  }
}

void Preprocessor::HandleInclude(std::string_view filename_raw, SourceLoc loc,
                                 int depth, std::string& output) {
  // Strip quotes: "file.sv" or <file.sv>
  auto fn = Trim(filename_raw);
  if (fn.size() >= 2 && (fn.front() == '"' || fn.front() == '<')) {
    fn = fn.substr(1, fn.size() - 2);
  }
  auto resolved = ResolveInclude(fn);
  if (resolved.empty()) {
    diag_.Error(loc, "cannot find include file '" + std::string(fn) + "'");
    return;
  }
  std::ifstream ifs(resolved);
  if (!ifs) {
    diag_.Error(loc, "cannot open include file '" + resolved + "'");
    return;
  }
  std::ostringstream ss;
  ss << ifs.rdbuf();
  auto content = ss.str();
  auto inc_id = src_mgr_.AddFile(resolved, content);
  output.append(ProcessSource(content, inc_id, depth + 1));
}

std::string Preprocessor::ExpandMacro(const MacroDef& macro,
                                      std::string_view args_text) {
  if (!macro.is_function_like) return macro.body;
  auto args = SplitMacroArgs(args_text);
  return SubstituteParams(macro.body, macro.params, args);
}

// --- Macro helper functions ---

std::vector<std::string> Preprocessor::ParseMacroParams(
    std::string_view param_list) {
  std::vector<std::string> params;
  size_t pos = 0;
  while (pos < param_list.size()) {
    auto comma = param_list.find(',', pos);
    if (comma == std::string_view::npos) comma = param_list.size();
    auto token = Trim(param_list.substr(pos, comma - pos));
    if (!token.empty()) {
      params.emplace_back(token);
    }
    pos = comma + 1;
  }
  return params;
}

std::string_view Preprocessor::ExtractBalancedArgs(std::string_view text) {
  auto open = text.find('(');
  if (open == std::string_view::npos) return {};
  int depth = 0;
  for (size_t i = open; i < text.size(); ++i) {
    if (text[i] == '(') ++depth;
    if (text[i] == ')') --depth;
    if (depth == 0) return text.substr(open, i - open + 1);
  }
  return {};
}

std::vector<std::string_view> Preprocessor::SplitMacroArgs(
    std::string_view args_text) {
  std::vector<std::string_view> args;
  int depth = 0;
  size_t start = 0;
  for (size_t i = 0; i < args_text.size(); ++i) {
    if (args_text[i] == '(') ++depth;
    if (args_text[i] == ')') --depth;
    if (args_text[i] == ',' && depth == 0) {
      args.push_back(Trim(args_text.substr(start, i - start)));
      start = i + 1;
    }
  }
  args.push_back(Trim(args_text.substr(start)));
  return args;
}

std::string Preprocessor::SubstituteParams(
    std::string_view body, const std::vector<std::string>& params,
    const std::vector<std::string_view>& args) {
  std::string result;
  result.reserve(body.size());
  size_t i = 0;
  while (i < body.size()) {
    if (!IsIdentChar(body[i])) {
      result += body[i++];
      continue;
    }
    size_t start = i;
    while (i < body.size() && IsIdentChar(body[i])) ++i;
    auto token = body.substr(start, i - start);
    bool replaced = false;
    for (size_t p = 0; p < params.size() && p < args.size(); ++p) {
      if (token == params[p]) {
        result.append(args[p]);
        replaced = true;
        break;
      }
    }
    if (!replaced) result.append(token);
  }
  return result;
}

std::string Preprocessor::ResolveInclude(std::string_view filename) {
  for (const auto& dir : config_.include_dirs) {
    auto path = dir + "/" + std::string(filename);
    std::ifstream ifs(path);
    if (ifs.good()) {
      return path;
    }
  }
  return "";
}

}  // namespace delta
