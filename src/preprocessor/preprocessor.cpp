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

bool Preprocessor::ProcessStateDirective(std::string_view line, SourceLoc loc) {
  if (StartsWithDirective(line, "timescale")) {
    HandleTimescale(AfterDirective(line, "timescale"), loc);
    return true;
  }
  if (StartsWithDirective(line, "resetall")) {
    macros_.UndefineAll();
    default_net_type_ = NetType::kWire;
    in_celldefine_ = false;
    unconnected_drive_ = NetType::kWire;
    return true;
  }
  if (StartsWithDirective(line, "default_nettype")) {
    HandleDefaultNettype(AfterDirective(line, "default_nettype"), loc);
    return true;
  }
  if (StartsWithDirective(line, "endcelldefine")) {
    in_celldefine_ = false;
    return true;
  }
  if (StartsWithDirective(line, "celldefine")) {
    in_celldefine_ = true;
    return true;
  }
  if (StartsWithDirective(line, "nounconnected_drive")) {
    unconnected_drive_ = NetType::kWire;
    return true;
  }
  if (StartsWithDirective(line, "unconnected_drive")) {
    HandleUnconnectedDrive(AfterDirective(line, "unconnected_drive"), loc);
    return true;
  }
  if (StartsWithDirective(line, "pragma")) {
    // Implementation-defined per IEEE 22.10; consume silently.
    return true;
  }
  if (StartsWithDirective(line, "line")) {
    HandleLine(AfterDirective(line, "line"), loc);
    return true;
  }
  if (StartsWithDirective(line, "begin_keywords")) {
    diag_.Warning(loc, "`begin_keywords not fully supported; ignored");
    return true;
  }
  if (StartsWithDirective(line, "end_keywords")) {
    diag_.Warning(loc, "`end_keywords not fully supported; ignored");
    return true;
  }
  return false;
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
  if (ProcessStateDirective(line, loc)) return true;
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

// --- Timescale parsing ---

static bool ParseTimescaleComponent(std::string_view text, int& magnitude,
                                    TimeUnit& unit) {
  auto trimmed = Trim(text);
  if (trimmed.empty()) return false;

  // Extract leading digits for magnitude.
  size_t i = 0;
  while (i < trimmed.size() &&
         std::isdigit(static_cast<unsigned char>(trimmed[i]))) {
    ++i;
  }
  if (i == 0) return false;

  int mag = 0;
  for (size_t j = 0; j < i; ++j) {
    mag = mag * 10 + (trimmed[j] - '0');
  }
  if (mag != 1 && mag != 10 && mag != 100) return false;
  magnitude = mag;

  auto unit_str = Trim(trimmed.substr(i));
  return ParseTimeUnitStr(unit_str, unit);
}

void Preprocessor::HandleTimescale(std::string_view rest, SourceLoc loc) {
  // Format: `timescale unit_mag unit / prec_mag precision
  auto slash = rest.find('/');
  if (slash == std::string_view::npos) {
    diag_.Error(loc, "invalid `timescale format: missing '/'");
    return;
  }
  auto unit_part = rest.substr(0, slash);
  auto prec_part = rest.substr(slash + 1);

  TimeScale ts;
  if (!ParseTimescaleComponent(unit_part, ts.magnitude, ts.unit)) {
    diag_.Error(loc, "invalid `timescale unit");
    return;
  }
  if (!ParseTimescaleComponent(prec_part, ts.prec_magnitude, ts.precision)) {
    diag_.Error(loc, "invalid `timescale precision");
    return;
  }

  current_timescale_ = ts;
  if (!has_timescale_ ||
      static_cast<int>(ts.precision) < static_cast<int>(global_precision_)) {
    global_precision_ = ts.precision;
  }
  has_timescale_ = true;
}

// --- default_nettype / unconnected_drive ---

static bool ParseNetTypeName(std::string_view name, NetType& out) {
  if (name == "wire") {
    out = NetType::kWire;
  } else if (name == "tri") {
    out = NetType::kTri;
  } else if (name == "wand") {
    out = NetType::kWand;
  } else if (name == "triand") {
    out = NetType::kTriand;
  } else if (name == "wor") {
    out = NetType::kWor;
  } else if (name == "trior") {
    out = NetType::kTrior;
  } else if (name == "tri0") {
    out = NetType::kTri0;
  } else if (name == "tri1") {
    out = NetType::kTri1;
  } else if (name == "uwire") {
    out = NetType::kUwire;
  } else {
    return false;
  }
  return true;
}

void Preprocessor::HandleDefaultNettype(std::string_view rest, SourceLoc loc) {
  auto name = Trim(rest);
  if (name == "none") {
    // `default_nettype none means no implicit nets.
    // We use kWire as the "none" sentinel since it's the default;
    // elaboration uses a separate flag. For now just track the value.
    default_net_type_ = NetType::kWire;
    return;
  }
  NetType nt = NetType::kWire;
  if (!ParseNetTypeName(name, nt)) {
    diag_.Error(loc, "invalid net type '" + std::string(name) + "'");
    return;
  }
  default_net_type_ = nt;
}

void Preprocessor::HandleUnconnectedDrive(std::string_view rest,
                                          SourceLoc loc) {
  auto arg = Trim(rest);
  if (arg == "pull0") {
    unconnected_drive_ = NetType::kTri0;
  } else if (arg == "pull1") {
    unconnected_drive_ = NetType::kTri1;
  } else {
    diag_.Error(
        loc, "invalid `unconnected_drive argument: '" + std::string(arg) + "'");
  }
}

void Preprocessor::HandleLine(std::string_view rest, SourceLoc loc) {
  // Format: number "filename" level
  auto trimmed = Trim(rest);
  size_t i = 0;
  while (i < trimmed.size() &&
         std::isdigit(static_cast<unsigned char>(trimmed[i]))) {
    ++i;
  }
  if (i == 0) {
    diag_.Warning(loc, "invalid `line directive: missing line number");
    return;
  }
  uint32_t new_line = 0;
  for (size_t j = 0; j < i; ++j) {
    new_line = new_line * 10 + (trimmed[j] - '0');
  }
  line_offset_ = new_line;
  has_line_override_ = true;
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
