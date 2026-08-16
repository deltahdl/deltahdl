#pragma once

// Internal declarations shared between the elaborator_validate*.cpp translation
// units that were split out of elaborator_validate.cpp. These helpers are
// file-local in spirit; the header exists only so that one translation unit can
// define a helper that another references, keeping a single definition of each
// symbol.

#include <cstdint>
#include <optional>
#include <string_view>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "common/diagnostic.h"
#include "elaborator/const_eval.h"
#include "elaborator/elaborator_helpers.h"
#include "elaborator/rtlir.h"
#include "parser/ast.h"

namespace delta {

using TypeMap = std::unordered_map<std::string_view, DataTypeKind>;
using NameSet = std::unordered_set<std::string_view>;

// Parses the size prefix of an integer literal's text (the digits before the
// base tick "'"). Returns that width when present and positive, otherwise the
// default unsized-literal width of 32. Defined in elaborator_validate.cpp.
uint32_t ExtractLiteralWidth(std::string_view text);

// Defined in elaborator_validate.cpp.
std::optional<int64_t> ComputeDimSize(const Expr* dim);
std::string_view LhsBaseName(const Expr* e);
bool ExprContainsIdent(const Expr* e, std::string_view name);
bool ExprUsesInterconnect(const Expr* e,
                          const std::unordered_set<std::string_view>& names);
void CheckNbaDynamicArrayTarget(
    const Stmt* s, const std::unordered_set<std::string_view>& dyn_names,
    const std::unordered_set<std::string_view>& dynsized_names,
    DiagEngine& diag);
void CollectProcTargets(const Stmt* s,
                        std::unordered_map<std::string_view, SourceLoc>& out);

void CollectForceReleaseTargets(
    const Stmt* s, std::unordered_map<std::string_view, SourceLoc>& out);
void CheckInterconnectProcContAssign(
    const Stmt* s,
    const std::unordered_set<std::string_view>& interconnect_names,
    DiagEngine& diag);
void CheckInterconnectProceduralRead(
    const Stmt* s,
    const std::unordered_set<std::string_view>& interconnect_names,
    DiagEngine& diag);
void CheckProceduralAssignLhs(const Stmt* s, DiagEngine& diag);
void CheckForceLhs(
    const Stmt* s, const std::unordered_set<std::string_view>& net_names,
    const std::unordered_set<std::string_view>& nettype_net_names,
    DiagEngine& diag);
using SelectShapeMap = std::unordered_map<std::string_view, VarSelectShape>;

// What §11.5.1 needs to judge the operand of a select. Its second alternative
// names two operands, "a real variable or real parameter", carried in separate
// sets because the report names the noun the clause gives the one it found and
// a parameter is not a variable. Each set holds only the names declared with no
// unpacked dimension, since §11.5.2 makes one address written after such a name
// an element select. `shapes` answers for the addresses after that one, which
// §11.5.2 sends back to §11.5.1 once the element is selected.
struct SelectOperands {
  const NameSet& variables;
  const NameSet& parameters;
  const SelectShapeMap& shapes;
};

// §11.5.1: `operands` decides the operand report. `types` is read for the index
// expression only, which the clause bars separately from being of real type.
void CheckRealSelect(const Expr* e, const TypeMap& types,
                     const SelectOperands& operands, DiagEngine& diag);
void CheckScalarSelect(const Expr* e, const NameSet& scalars, DiagEngine& diag);
void CheckIndexedPartSelectWidth(const Expr* e, const ScopeMap& scope,
                                 DiagEngine& diag);
void CheckScalarSelectStmt(const Stmt* s, const NameSet& scalars,
                           DiagEngine& diag);
void CheckRealSelectStmt(const Stmt* s, const TypeMap& types,
                         const SelectOperands& operands, DiagEngine& diag);
void CheckIndexedPartSelectWidthStmt(const Stmt* s, const ScopeMap& scope,
                                     DiagEngine& diag);

// Defined in elaborator_validate_matches.cpp.
bool IsArrayQueryFunc(std::string_view callee);
bool TypedefHasDynamicDim(const std::vector<Expr*>& dims);

}  // namespace delta
