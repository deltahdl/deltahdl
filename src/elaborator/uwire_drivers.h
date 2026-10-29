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

// One step from a uwire net toward the bits a driver reaches: a member of the
// net's structure, or the indices a constant select names in the next of its
// dimensions. A driver of the whole net takes no step.
struct UwireStep {
  std::string_view member;
  int64_t lo = 0;
  int64_t hi = 0;
};
using UwirePath = std::vector<UwireStep>;

// §6.6.2 (printed page 92): no bit of a uwire net shall be connected to more
// than one driver. The uwire nets of one scope -- a module, interface or
// program with its generate blocks, or a compilation unit -- and what of each
// the scope's drivers have reached so far: a continuous assignment's target, a
// net declaration assignment, and the output terminal of a gate, a UDP or a
// unidirectional switch. Keyed by the declaration a net's name binds.
class UwireDrivers {
 public:
  void Declare(std::string_view declared) { nets_.try_emplace(declared); }
  [[nodiscard]] bool Declares(std::string_view declared) const {
    return nets_.count(declared) != 0;
  }

  // Records a driver standing at `loc` as reaching `path` of the uwire net
  // `declared`, which the source names `name`, and reports it under §6.6.2
  // where an earlier driver reaches one of the same bits.
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

// The drivers of the uwire nets each compilation unit declares, which the
// module instances throughout the design drive.
using UnitUwireDrivers =
    std::unordered_map<const CompilationUnit*, UwireDrivers>;

// How many drivers of each uwire net every compilation unit's drivers hold.
using UnitUwireCounts =
    std::unordered_map<const CompilationUnit*,
                       std::unordered_map<std::string_view, size_t>>;
UnitUwireCounts CountUnitUwireDrivers(const UnitUwireDrivers& units);

// §23.3.2: each element of an array of module instances is an instance of
// its own, elaborated once for all of them, so where the instantiation at
// `loc` makes more than one of its `elements`, each driver of a compilation
// unit's uwire net recorded among `units` since `counts` is recorded again for
// the elements after the first, standing at `loc`.
void RepeatUnitUwireDrivers(UnitUwireDrivers& units,
                            const UnitUwireCounts& counts, uint32_t elements,
                            SourceLoc loc, DiagEngine& diag);

// Where a driver's target names its net: the scope's module, the types of its
// variables and nets, the compilation unit around it with that unit's drivers,
// the generate blocks enclosing the target with the names they declare, and
// the parameters and genvars a select may read.
struct UwireTargetScope {
  const RtlirModule* mod;
  const std::unordered_map<std::string_view, DataTypeKind>& types;
  const CompilationUnit* unit;
  UnitUwireDrivers& unit_drivers;
  ScopedDeclarations names;
  const ScopeMap& constants;
};

// Records each element of `target` that names a uwire net as a driver
// standing at `loc`, a concatenation's elements one by one, among the scope's
// `drivers` or its compilation unit's. A target reached through a select that
// is not constant, which Table 10-1 reports, is not recorded.
void RecordUwireTarget(UwireDrivers& drivers, const Expr* target, SourceLoc loc,
                       const UwireTargetScope& in, DiagEngine& diag);

// Records the output terminals of the gate, switch or UDP instance `item` as
// drivers, a terminal an instance array connects whole to each of its
// instances (§28.3.6) as one driver per instance. A bidirectional pass switch
// drives no terminal of its own, §6.6.2 barring a uwire net from its terminals
// outright.
void RecordUwirePrimitiveOutputs(UwireDrivers& drivers, const ModuleItem* item,
                                 const UwireTargetScope& in, DiagEngine& diag);

}  // namespace delta
