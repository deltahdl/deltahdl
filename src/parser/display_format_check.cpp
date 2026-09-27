#include "parser/display_format_check.h"

#include <cctype>
#include <cstddef>
#include <format>
#include <string_view>

#include "common/diagnostic.h"
#include "parser/ast_expr.h"

namespace delta {

namespace {

// §21.2's display and write tasks, §21.2.2's strobe and §21.2.3's monitor
// tasks, the file forms §21.3.2 gives each of them, §21.3.3's $swrite family,
// which "accepts the same type of arguments" as $fwrite, and §20.10's severity
// tasks, whose message has "the same syntax as $display". Every string literal
// argument of one is a format.
bool IsFormatListTask(std::string_view name) {
  static constexpr std::string_view kStems[] = {
      "display", "write",   "strobe",   "monitor", "fdisplay",
      "fwrite",  "fstrobe", "fmonitor", "swrite"};
  static constexpr std::string_view kSeverity[] = {"$error", "$warning",
                                                   "$info", "$fatal"};
  for (std::string_view task : kSeverity) {
    if (name == task) return true;
  }
  if (!name.starts_with('$')) return false;
  name.remove_prefix(1);
  if (name.ends_with('b') || name.ends_with('o') || name.ends_with('h')) {
    for (std::string_view stem : kStems) {
      if (name.substr(0, name.size() - 1) == stem) return true;
    }
  }
  for (std::string_view stem : kStems) {
    if (name == stem) return true;
  }
  return false;
}

// The text a string literal's quotes enclose; §5.9 gives the literal a quoted
// and a triple-quoted spelling.
std::string_view LiteralBody(std::string_view text) {
  if (text.size() >= 6 && text.starts_with("\"\"\""))
    return text.substr(3, text.size() - 6);
  if (text.size() >= 2 && text.front() == '"')
    return text.substr(1, text.size() - 2);
  return text;
}

// Table 21-1's specifiers and Table 21-2's real ones, each in either case.
bool IsDefinedSpecifier(char c) {
  static constexpr std::string_view kDefined = "hxdobclvmpstuzefg";
  return kDefined.find(static_cast<char>(std::tolower(
             static_cast<unsigned char>(c)))) != std::string_view::npos;
}

// §21.2.1.1 (printed page 658): Table 21-2's real specifiers "have the full
// formatting capabilities available in the C language", its flags among them;
// no other specifier takes one.
bool IsRealSpecifier(char c) {
  char lower = static_cast<char>(std::tolower(static_cast<unsigned char>(c)));
  return lower == 'e' || lower == 'f' || lower == 'g';
}

bool IsCFlag(char c) { return c == '-' || c == '+' || c == ' ' || c == '#'; }

size_t SkipDigits(std::string_view fmt, size_t j) {
  while (j < fmt.size() && std::isdigit(static_cast<unsigned char>(fmt[j])))
    ++j;
  return j;
}

// Where the conversion whose `%` is at `i` ends: past any C flags, the field
// width §21.2.1.2 allows and a precision, at the letter -- or at the end of
// the literal, where the runtime reads a bare width as the decimal conversion.
// `flagged` says whether any flag was written.
size_t ConversionLetter(std::string_view fmt, size_t i, bool& flagged) {
  size_t j = i + 1;
  while (j < fmt.size() && IsCFlag(fmt[j])) ++j;
  flagged = j > i + 1;
  j = SkipDigits(fmt, j);
  if (j < fmt.size() && fmt[j] == '.') j = SkipDigits(fmt, j + 1);
  return j;
}

// The walk the display tasks make of a format (FormatDisplay in the
// simulator): a backslash escape's next character is text, `%%` is a percent
// sign, and a `%` ending the literal is text.
void CheckFormatLiteral(const Expr* lit, std::string_view task,
                        DiagEngine& diag) {
  std::string_view fmt = LiteralBody(lit->text);
  for (size_t i = 0; i + 1 < fmt.size(); ++i) {
    if (fmt[i] == '\\') {
      ++i;
      continue;
    }
    if (fmt[i] != '%') continue;
    if (fmt[i + 1] == '%') {
      ++i;
      continue;
    }
    bool flagged = false;
    size_t j = ConversionLetter(fmt, i, flagged);
    bool at_end = j >= fmt.size();
    bool defined = at_end ? !flagged
                          : IsDefinedSpecifier(fmt[j]) &&
                                (!flagged || IsRealSpecifier(fmt[j]));
    if (!defined) {
      diag.Error(lit->range.start,
                 std::format("undefined format specifier '{}' in a string "
                             "literal argument of {}",
                             fmt.substr(i, at_end ? j - i : j - i + 1), task),
                 Subclause("21.2.1.1"));
    }
    i = j;
  }
}

void CheckIfLiteral(const Expr* arg, std::string_view task, DiagEngine& diag) {
  if (arg != nullptr && arg->kind == ExprKind::kStringLiteral)
    CheckFormatLiteral(arg, task, diag);
}

}  // namespace

void CheckDisplayFormatLiterals(const Expr* call, DiagEngine& diag) {
  std::string_view task = call->callee;
  // §21.3.3: $sformat "always interprets its second argument, and only its
  // second argument, as a format string", and $sformatf "behaves like
  // $sformat" with the format first.
  if (task == "$sformat") {
    if (call->args.size() > 1) CheckIfLiteral(call->args[1], task, diag);
    return;
  }
  if (task == "$sformatf") {
    if (!call->args.empty()) CheckIfLiteral(call->args[0], task, diag);
    return;
  }
  if (!IsFormatListTask(task)) return;
  for (const Expr* arg : call->args) CheckIfLiteral(arg, task, diag);
}

}  // namespace delta
