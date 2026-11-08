#pragma once

#include <string_view>
#include <unordered_set>
#include <utility>

#include "parser/parser.h"
#include "parser/scope_type_names.h"

namespace delta {

class TypeNameScope {
 public:
  explicit TypeNameScope(Parser& p)
      : parser_(p),
        saved_types_(p.known_types_),
        saved_nettypes_(p.known_nettypes_) {}
  ~TypeNameScope() {
    parser_.known_types_ = std::move(saved_types_);
    parser_.known_nettypes_ = std::move(saved_nettypes_);
  }
  TypeNameScope(const TypeNameScope&) = delete;
  TypeNameScope& operator=(const TypeNameScope&) = delete;

  ScopeTypeNames NamesAddedSoFar() const {
    ScopeTypeNames added;
    for (auto name : parser_.known_types_) {
      if (saved_types_.count(name) == 0) added.types.insert(name);
    }
    for (auto name : parser_.known_nettypes_) {
      if (saved_nettypes_.count(name) == 0) added.nettypes.insert(name);
    }
    return added;
  }

 private:
  Parser& parser_;
  std::unordered_set<std::string_view> saved_types_;
  std::unordered_set<std::string_view> saved_nettypes_;
};

}  // namespace delta
