#pragma once

#include <cstdint>
#include <optional>
#include <string_view>
#include <utility>
#include <vector>

#include "parser/ast_type.h"

namespace delta {

struct Expr;
struct ModuleItem;

// One dimension of a DPI formal argument or function result, reduced to the
// two bounds its declaration gives it. §35.5.4 rules that the type of an
// argument "includes dimensions and bounds of any arrays or array
// dimensions", so a signature that recorded a dimension's presence without
// its bounds would let `bit [7:0]` and `bit [15:0]` share one signature.
//
// A bound is recorded as the constant it evaluates to, which is what makes
// [7:0] and [3+4:0] one dimension rather than two. A bound that does not fold
// is recorded as absent, and two absent bounds compare equal: nothing finer is
// available here, and reporting a disagreement between two bounds neither of
// which has a value would reject a conforming design.
struct DpiDimension {
  // The "[]" form, which states no bounds at all rather than bounds that
  // failed to fold.
  bool is_unsized = false;
  std::optional<int64_t> left;
  std::optional<int64_t> right;
  bool operator==(const DpiDimension&) const = default;
};

// The part of a declared type that §35.5.4 puts into a signature: what the
// type is, and every dimension written on it. Packed and unpacked dimensions
// are held apart because a formal declaring one of each is a different type
// from one declaring two of either.
struct DpiTypeShape {
  DataTypeKind kind = DataTypeKind::kImplicit;
  bool has_unsized_packed_dim = false;
  std::vector<DpiDimension> packed_dims;
  std::vector<DpiDimension> unpacked_dims;
  bool operator==(const DpiTypeShape&) const = default;
};

// §35.5.4 enumerates the parts of the type signature that must match across
// every declaration sharing one linkage name: the return type, the number,
// order, direction and type of each argument, the pure/context qualifiers and
// the dpi_spec_string. Argument names and default values are absent by
// design, the clause permitting those to vary between scopes.
struct DpiSignatureKey {
  DpiTypeShape return_type;
  bool is_pure = false;
  bool is_context = false;
  bool is_task = false;
  std::string_view spec_string;
  std::vector<std::pair<Direction, DpiTypeShape>> args;
};

// §35.4: an export declaration borrows its type signature from the
// SystemVerilog function or task it names. The parts that matter for
// equivalence — the return type, the function-versus-task distinction, and
// each formal argument's direction and type — are extracted here so that two
// exports sharing one linkage identifier across scopes can be compared
// without paying attention to identifiers, default values, or other
// non-signature details.
struct DpiExportSignature {
  DpiTypeShape return_type;
  bool is_task = false;
  std::vector<std::pair<Direction, DpiTypeShape>> args;
  bool operator==(const DpiExportSignature&) const = default;
};

// §35.5.4: the linkage name is the explicit c_identifier when given, otherwise
// it defaults to the SystemVerilog subroutine name.
std::string_view DpiLinkageName(const ModuleItem* item);

// The shape a type contributes to a signature. `unpacked_dims` are the
// dimensions written after the declared name, which only a formal argument
// has; a function result passes an empty list.
DpiTypeShape BuildDpiTypeShape(const DataType& type,
                               const std::vector<Expr*>& unpacked_dims);

DpiSignatureKey BuildDpiSignature(const ModuleItem* item);

bool DpiSignaturesMatch(const DpiSignatureKey& a, const DpiSignatureKey& b);

DpiExportSignature BuildDpiExportSignature(const ModuleItem* callable);

}  // namespace delta
