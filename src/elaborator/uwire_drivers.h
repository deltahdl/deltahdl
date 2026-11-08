#pragma once

#include <cstddef>
#include <cstdint>
#include <string_view>
#include <unordered_map>
#include <vector>

#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "elaborator/const_eval.h"
#include "elaborator/rtlir.h"
#include "elaborator/rtlir_scopes.h"
#include "parser/ast_design.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_type.h"

namespace delta {

struct UwireStep {
  std::string_view member;
  int64_t lo = 0;
  int64_t hi = 0;
};
using UwirePath = std::vector<UwireStep>;

class UwireDrivers {
 public:
  void Declare(std::string_view declared) { nets_.try_emplace(declared); }
  [[nodiscard]] bool Declares(std::string_view declared) const {
    return nets_.count(declared) != 0;
  }

  void Record(std::string_view name, std::string_view declared,
              const UwirePath& path, SourceLoc loc, DiagEngine& diag);

  void Clear() { nets_.clear(); }

  [[nodiscard]] const std::unordered_map<std::string_view,
                                         std::vector<UwirePath>>&
  Nets() const {
    return nets_;
  }

 private:
  std::unordered_map<std::string_view, std::vector<UwirePath>> nets_;
};

using UnitUwireDrivers =
    std::unordered_map<const CompilationUnit*, UwireDrivers>;

using UnitUwireCounts =
    std::unordered_map<const CompilationUnit*,
                       std::unordered_map<std::string_view, size_t>>;
UnitUwireCounts CountUnitUwireDrivers(const UnitUwireDrivers& units);

void RepeatUnitUwireDrivers(UnitUwireDrivers& units,
                            const UnitUwireCounts& counts, uint32_t elements,
                            SourceLoc loc, DiagEngine& diag);

struct UwireTargetScope {
  const RtlirModule* mod;
  const std::unordered_map<std::string_view, DataTypeKind>& types;
  const CompilationUnit* unit;
  UnitUwireDrivers& unit_drivers;
  ScopedDeclarations names;
  const ScopeMap& constants;
};

void RecordUwireTarget(UwireDrivers& drivers, const Expr* target, SourceLoc loc,
                       const UwireTargetScope& in, DiagEngine& diag);

void RecordUwirePrimitiveOutputs(UwireDrivers& drivers, const ModuleItem* item,
                                 const UwireTargetScope& in, DiagEngine& diag);

}  // namespace delta
