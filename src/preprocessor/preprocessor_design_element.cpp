#include <cctype>
#include <cstddef>
#include <string>
#include <string_view>
#include <vector>

#include "preprocessor/preprocessor.h"

// The design elements a preprocessed line opens and closes (§3.2), and what
// the preprocessor records at each one's header: the directives in force there
// (§22.7, Annex E) and, inside `celldefine, its cell mark (§22.10).

namespace delta {

static std::string_view ExtractModuleName(std::string_view trimmed,
                                          std::string_view keyword) {
  auto rest = trimmed.substr(keyword.size());

  if (rest.starts_with("automatic ")) rest = rest.substr(10);
  // Every caller hands a trimmed line, whose last character is not white
  // space, so the skip stops before the text runs out.
  while (rest[0] == ' ' || rest[0] == '\t') rest.remove_prefix(1);
  size_t end = 0;
  while (end < rest.size() && rest[end] != ' ' && rest[end] != '\t' &&
         rest[end] != '(' && rest[end] != ';' && rest[end] != '#')
    ++end;
  return rest.substr(0, end);
}

// Returns the leading whitespace-delimited word of `trimmed`.
static std::string_view FirstWord(std::string_view trimmed) {
  size_t end = 0;
  while (end < trimmed.size() &&
         !std::isspace(static_cast<unsigned char>(trimmed[end]))) {
    ++end;
  }
  return trimmed.substr(0, end);
}

// True when `rest` opens with the whole word `word`.
static bool StartsWithWord(std::string_view rest, std::string_view word) {
  if (!rest.starts_with(word)) return false;
  return rest.size() == word.size() || !IsIdentChar(rest[word.size()]);
}

// §3.2 names the design elements: module, macromodule, program, interface,
// checker, package, primitive, and configuration. The keyword is matched as
// the line's first word so that any whitespace may separate it from the name
// that follows, and something must follow — a keyword standing alone on a line
// names no element. An interface class is a class rather than an interface —
// it is closed by endclass, not endinterface — so it opens no design element.
static bool IsDesignElementStart(std::string_view trimmed) {
  static constexpr std::string_view kKeywords[] = {
      "module",  "macromodule", "program",   "interface",
      "checker", "package",     "primitive", "config",
  };
  auto word = FirstWord(trimmed);
  bool is_keyword = false;
  for (auto keyword : kKeywords) {
    if (word == keyword) {
      is_keyword = true;
      break;
    }
  }
  if (!is_keyword) return false;

  auto rest = Preprocessor::Trim(trimmed.substr(word.size()));
  if (rest.empty()) return false;
  if (word == "interface" && StartsWithWord(rest, "class")) return false;
  return true;
}

// A.1.2 lets attribute instances stand before a design element's keyword, and
// one may run across lines. The text after those that open `trimmed`, or
// nothing while one is still open; `open` says on entry whether one was left
// open on an earlier line, and on return whether one is open at this line's
// end. An attribute_instance's first attr_spec is a name, so `(*)` is the
// event control of §9.4.2.2 rather than the opening of one.
static std::string_view AfterAttributeInstances(std::string_view trimmed,
                                                bool& open) {
  if (open) {
    size_t close = trimmed.find("*)");
    if (close == std::string_view::npos) return {};
    open = false;
    trimmed = Preprocessor::Trim(trimmed.substr(close + 2));
  }
  while (trimmed.starts_with("(*") && !trimmed.starts_with("(*)")) {
    size_t close = trimmed.find("*)", 2);
    if (close == std::string_view::npos) {
      open = true;
      return {};
    }
    trimmed = Preprocessor::Trim(trimmed.substr(close + 2));
  }
  return trimmed;
}

// The position just past the `: name` that may label an end keyword ending at
// `pos`, or `pos` itself when no label follows.
// `text` is trimmed, so a trimmed tail of it keeps its end where `text` does.
static size_t PastEndLabel(std::string_view text, size_t pos) {
  auto rest = Preprocessor::Trim(text.substr(pos));
  if (!rest.starts_with(':')) return pos;
  rest = Preprocessor::Trim(rest.substr(1));
  size_t name = 0;
  while (name < rest.size() && IsIdentChar(rest[name])) ++name;
  return text.size() - rest.size() + name;
}

// The position just past the first word of `text` that ends a design element,
// and past its label, or npos when no word of `text` ends one.
static size_t PastDesignElementEnd(std::string_view text) {
  static constexpr std::string_view kEndKeywords[] = {
      "endmodule",  "endprogram",   "endinterface", "endchecker",
      "endpackage", "endprimitive", "endconfig",
  };
  size_t i = 0;
  while (i < text.size()) {
    if (!IsIdentChar(text[i])) {
      ++i;
      continue;
    }
    size_t end = i;
    while (end < text.size() && IsIdentChar(text[end])) ++end;
    auto word = text.substr(i, end - i);
    for (auto keyword : kEndKeywords) {
      if (word == keyword) return PastEndLabel(text, end);
    }
    i = end;
  }
  return std::string_view::npos;
}

static void TrackCellModuleName(std::string_view trimmed,
                                std::vector<std::string>& cell_module_names) {
  if (trimmed.starts_with("module ")) {
    auto name = ExtractModuleName(trimmed, "module ");
    if (!name.empty()) cell_module_names.emplace_back(name);
  } else if (trimmed.starts_with("macromodule ")) {
    auto name = ExtractModuleName(trimmed, "macromodule ");
    if (!name.empty()) cell_module_names.emplace_back(name);
  }
}

// The design element a header line declares, with an empty name for a header
// of another kind. Modules, interfaces, programs and packages are what
// §3.14.2.3 gives a time unit and precision of their own. The first three are
// parsed into a ModuleDecl and a package into a PackageDecl, and a package's
// name lives in a name space of its own (§3.13), so the record says which.
namespace {
struct DeclaredElement {
  std::string_view name;
  bool is_package = false;
};
}  // namespace

static DeclaredElement DeclaredElementAt(std::string_view trimmed) {
  for (std::string_view keyword :
       {"module ", "macromodule ", "interface ", "program "}) {
    if (trimmed.starts_with(keyword))
      return {ExtractModuleName(trimmed, keyword), false};
  }
  if (trimmed.starts_with("package "))
    return {ExtractModuleName(trimmed, "package "), true};
  return {};
}

void Preprocessor::TrackDesignElementHeader(std::string_view trimmed) {
  if (IsDesignElementStart(trimmed)) {
    if (in_celldefine_) TrackCellModuleName(trimmed, cell_module_names_);
    // Annex E: each of its directives applies to the modules that follow
    // it, so the decay time, charge strength and delay mode in force at this
    // header are the ones this module takes, whatever a later directive sets.
    // §22.7 (printed page 716) rules the same of `timescale, which "specifies
    // the time unit and time precision of the design elements that follow it".
    DeclaredElement element = DeclaredElementAt(trimmed);
    if (!element.name.empty()) {
      module_directives_.push_back(
          {std::string(element.name), default_decay_time_,
           default_decay_time_infinite_, default_trireg_strength_,
           has_default_trireg_strength_, delay_mode_directive_, has_timescale_,
           current_timescale_, element.is_package});
    }
    ++design_element_depth_;
  }
}

// A header need not open its line: attribute instances may come before it, and
// an earlier element may end on the same line. So the line is taken element by
// element, each piece starting where the previous one's end keyword left off.
void Preprocessor::TrackDesignElement(std::string_view trimmed) {
  while (true) {
    TrackDesignElementHeader(
        AfterAttributeInstances(trimmed, in_attribute_instance_));
    size_t past_end = PastDesignElementEnd(trimmed);
    if (past_end == std::string_view::npos) return;
    if (design_element_depth_ > 0) --design_element_depth_;
    trimmed = Trim(trimmed.substr(past_end));
  }
}

}  // namespace delta
