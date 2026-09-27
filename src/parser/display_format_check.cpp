#include "parser/display_format_check.h"

#include <cctype>
#include <cstddef>
#include <cstdint>
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

// What a conversion is: one Table 21-1 or Table 21-2 defines, one whose letter
// neither table defines, or a defined integer letter behind a C flag.
enum class Conversion : uint8_t { kDefined, kUndefined, kFlaggedWidth };

// The conversion whose letter is at `j`, or which the literal's end cut short
// there. §21.2.1.2 (printed page 659) has only "a non-negative decimal integer
// constant" between the % and an integer specifier's letter, so a flag before
// one, `%-6d`, is no field width; the letter itself is still Table 21-1's.
Conversion ClassifyConversion(std::string_view fmt, size_t j, bool flagged) {
  if (j >= fmt.size()) {
    return flagged ? Conversion::kUndefined : Conversion::kDefined;
  }
  if (!IsDefinedSpecifier(fmt[j])) return Conversion::kUndefined;
  if (flagged && !IsRealSpecifier(fmt[j])) return Conversion::kFlaggedWidth;
  return Conversion::kDefined;
}

// §21.2.1.1 (printed page 656) makes an undefined format specifier an error.
// A flagged integer specifier breaks §21.2.1.2's field width rule instead,
// which names no error, and is warned about.
void ReportConversion(const Expr* lit, std::string_view spec,
                      Conversion conversion, std::string_view task,
                      DiagEngine& diag) {
  if (conversion == Conversion::kUndefined) {
    diag.Error(lit->range.start,
               std::format("undefined format specifier '{}' in a string "
                           "literal argument of {}",
                           spec, task),
               Subclause("21.2.1.1"));
  } else if (conversion == Conversion::kFlaggedWidth) {
    diag.Warning(lit->range.start,
                 std::format("field width of '{}' in a string literal "
                             "argument of {} is not a non-negative decimal "
                             "integer constant",
                             spec, task),
                 Subclause("21.2.1.2"));
  }
}

// The walk the display tasks make of a format (FormatDisplay in the
// simulator): a backslash escape's next character is text, `%%` is a percent
// sign, and a `%` ending the literal is text.
void CheckFormatLiteral(const Expr* lit, std::string_view task,
                        DiagEngine& diag) {
  std::string_view fmt = LiteralBody(lit->text);
  for (size_t i = 0; i + 1 < fmt.size(); ++i) {
    if (fmt[i] == '\\' || (fmt[i] == '%' && fmt[i + 1] == '%')) {
      ++i;
      continue;
    }
    if (fmt[i] != '%') continue;
    bool flagged = false;
    size_t j = ConversionLetter(fmt, i, flagged);
    size_t end = j >= fmt.size() ? j : j + 1;
    ReportConversion(lit, fmt.substr(i, end - i),
                     ClassifyConversion(fmt, j, flagged), task, diag);
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
