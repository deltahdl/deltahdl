#include "parser/display_format_check.h"

#include <cctype>
#include <cstddef>
#include <format>
#include <string_view>

#include "common/diagnostic.h"
#include "parser/ast_expr.h"

namespace delta {

namespace {

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

std::string_view LiteralBody(std::string_view text) {
  if (text.size() >= 6 && text.starts_with("\"\"\""))
    return text.substr(3, text.size() - 6);
  if (text.size() >= 2 && text.front() == '"')
    return text.substr(1, text.size() - 2);
  return text;
}

bool IsDefinedSpecifier(char c) {
  static constexpr std::string_view kDefined = "hxdobclvmpstuzefg";
  return kDefined.find(static_cast<char>(std::tolower(
             static_cast<unsigned char>(c)))) != std::string_view::npos;
}

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

size_t ConversionLetter(std::string_view fmt, size_t i, bool& flagged) {
  size_t j = i + 1;
  while (j < fmt.size() && IsCFlag(fmt[j])) ++j;
  flagged = j > i + 1;
  j = SkipDigits(fmt, j);
  if (j < fmt.size() && fmt[j] == '.') j = SkipDigits(fmt, j + 1);
  return j;
}

bool IsDefinedConversion(std::string_view fmt, size_t j, bool flagged) {
  if (j >= fmt.size()) return !flagged;
  return IsDefinedSpecifier(fmt[j]) && (!flagged || IsRealSpecifier(fmt[j]));
}

void ReportUndefinedConversion(const Expr* lit, std::string_view spec,
                               std::string_view task, DiagEngine& diag) {
  diag.Error(lit->range.start,
             std::format("undefined format specifier '{}' in a string "
                         "literal argument of {}",
                         spec, task),
             Subclause("21.2.1.1"));
}

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
    if (!IsDefinedConversion(fmt, j, flagged))
      ReportUndefinedConversion(lit, fmt.substr(i, end - i), task, diag);
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
