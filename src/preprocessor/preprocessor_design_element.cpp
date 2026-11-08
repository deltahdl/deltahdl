#include <cctype>
#include <cstddef>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "preprocessor/preprocessor.h"

namespace delta {

static std::string_view FirstWord(std::string_view trimmed) {
  size_t end = 0;
  while (end < trimmed.size() &&
         !std::isspace(static_cast<unsigned char>(trimmed[end]))) {
    ++end;
  }
  return trimmed.substr(0, end);
}

static bool StartsWithWord(std::string_view rest, std::string_view word) {
  if (!rest.starts_with(word)) return false;
  return rest.size() == word.size() || !IsIdentChar(rest[word.size()]);
}

static std::string_view PastHeaderKeyword(std::string_view trimmed,
                                          std::string_view word) {
  std::string_view rest = Preprocessor::Trim(trimmed.substr(word.size()));
  for (std::string_view lifetime : {"static", "automatic"}) {
    if (StartsWithWord(rest, lifetime))
      rest = Preprocessor::Trim(rest.substr(lifetime.size()));
  }
  return rest;
}

static std::string_view HeaderName(std::string_view trimmed,
                                   std::string_view word) {
  std::string_view rest = PastHeaderKeyword(trimmed, word);
  size_t end = 0;
  while (end < rest.size() &&
         !std::isspace(static_cast<unsigned char>(rest[end])) &&
         rest[end] != '(' && rest[end] != ';' && rest[end] != '#')
    ++end;
  return rest.substr(0, end);
}

static bool IsDesignElementKeyword(std::string_view word) {
  static constexpr std::string_view kKeywords[] = {
      "module",  "macromodule", "program",   "interface",
      "checker", "package",     "primitive", "config",
  };
  for (auto keyword : kKeywords) {
    if (word == keyword) return true;
  }
  return false;
}

static bool IsDesignElementStart(std::string_view trimmed) {
  auto word = FirstWord(trimmed);
  if (!IsDesignElementKeyword(word)) return false;

  auto rest = Preprocessor::Trim(trimmed.substr(word.size()));
  if (rest.empty()) return false;
  if (word == "interface" && StartsWithWord(rest, "class")) return false;
  return true;
}

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

static size_t PastEndLabel(std::string_view text, size_t pos) {
  auto rest = Preprocessor::Trim(text.substr(pos));
  if (!rest.starts_with(':')) return pos;
  rest = Preprocessor::Trim(rest.substr(1));
  size_t name = 0;
  while (name < rest.size() && IsIdentChar(rest[name])) ++name;
  return text.size() - rest.size() + name;
}

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
  std::string_view word = FirstWord(trimmed);
  if (word != "module" && word != "macromodule") return;
  std::string_view name = HeaderName(trimmed, word);
  if (!name.empty()) cell_module_names.emplace_back(name);
}

namespace {
struct DeclaredElement {
  std::string_view name;
  bool is_package = false;
};
}  // namespace

static DeclaredElement DeclaredElementAt(std::string_view trimmed) {
  std::string_view word = FirstWord(trimmed);
  if (word == "package") return {HeaderName(trimmed, word), true};
  for (std::string_view keyword :
       {"module", "macromodule", "interface", "program"}) {
    if (word == keyword) return {HeaderName(trimmed, word), false};
  }
  return {};
}

static bool IsHeaderAwaitingItsName(std::string_view trimmed) {
  std::string_view word = FirstWord(trimmed);
  return IsDesignElementKeyword(word) &&
         PastHeaderKeyword(trimmed, word).empty();
}

void Preprocessor::TrackDesignElementHeader(std::string_view trimmed) {
  if (IsHeaderAwaitingItsName(trimmed)) {
    pending_header_ = std::string(trimmed);
    return;
  }
  if (IsDesignElementStart(trimmed)) {
    if (in_celldefine_) TrackCellModuleName(trimmed, cell_module_names_);
    DeclaredElement element = DeclaredElementAt(trimmed);
    if (!element.name.empty()) {
      module_directives_.push_back(
          {std::string(element.name), default_decay_time_,
           default_decay_time_infinite_, default_trireg_strength_,
           has_default_trireg_strength_, delay_mode_directive_, has_timescale_,
           current_timescale_, element.is_package, default_net_type_,
           unconnected_drive_, default_decay_time_is_real_,
           default_decay_time_real_});
    }
    ++design_element_depth_;
  }
}

void Preprocessor::TrackDesignElement(std::string_view trimmed) {
  if (!pending_header_.empty()) {
    std::string header = std::move(pending_header_);
    pending_header_.clear();
    TrackDesignElement(header + " " + std::string(trimmed));
    return;
  }
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
