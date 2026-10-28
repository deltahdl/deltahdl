#pragma once

#include <cstdint>
#include <functional>
#include <optional>
#include <string>
#include <string_view>
#include <unordered_map>
#include <vector>

#include "common/types.h"
#include "elaborator/rtlir_attribute.h"
#include "elaborator/rtlir_scopes.h"
#include "simulator/vpi_design_attach_build.h"
#include "simulator/vpi_object.h"

namespace delta {

class SimContext;
struct Expr;

// The expression builder of vpi_design_attach_assigns.cpp, shared with the
// continuous assignment pass of vpi_design_attach_cont_assigns.cpp, which
// builds each assignment's two sides through it.

// Where the names of one assignment resolve: the instance it was elaborated
// in, keyed as the simulator keys it; the generate blocks it stands in,
// innermost last, whose declarations a name finds first; and, for an
// expression a procedure's statement writes, the block or statement it stands
// in, whose blocks' declarations a name finds ahead of all of those.
struct AssignNames {
  const std::unordered_map<std::string_view, VpiObject*>& objects;
  const std::string& prefix;
  const GenBlockPrefixes& gen;
  const VpiObject* scope = nullptr;
  // §27.4: the genvars of the loop generate blocks a continuous assignment
  // stands in, each with the value it holds in the block instance; none for
  // any other expression.
  const GenBlockConsts& genvars = NoGenvars();
  // The instance object a continuous assignment stands in, where `scope` is
  // none; a top's prefix is empty and keys no object.
  const VpiObject* instance = nullptr;
  // §26.3: the imports of the module the expression is written in, through
  // which a name it does not declare may name a package's let (§11.12); none
  // for an expression of no module.
  const std::vector<RtlirImport>& imports = NoImports();
  // §3.12.1: the compilation unit the module the expression is written in
  // was declared in, whose declarations its names reach after the imports'
  // (UnitScopes::ScopeName); -1 for a design of one unit.
  int unit = -1;
  // §37.25: the typespecs of the compilation unit's and the packages' typedefs
  // (VpiAttachBuild::unit_typespecs), which a type a cast names may be.
  const VpiObjectMap& unit_typespecs = VpiAttachBuild::NoTypespecs();

  static const GenBlockConsts& NoGenvars() {
    static const GenBlockConsts kNone;
    return kNone;
  }
  static const std::vector<RtlirImport>& NoImports() {
    static const std::vector<RtlirImport> kNone;
    return kNone;
  }
};

// §23.9 and §27.4: the net, variable or other object the name `name` stands
// for where `names` places it: a declaration of the blocks around the scope,
// innermost first, then of the generate blocks it stands in, then of the
// instance; null where none is.
VpiHandle Resolve(const AssignNames& names, std::string_view name);

// What building one assignment's expressions needs: somewhere to allocate an
// object, the run a constant's value is evaluated in, the names, and the
// functions the calls in them resolve to.
struct AssignBuild {
  std::function<VpiObject*()> alloc;
  SimContext* sim;
  AssignNames names;
  VpiCalleeResolver callees;
  std::function<std::string_view(std::string)> keep;
  std::function<bool(const Expr&, VpiObject*)> shape_call = nullptr;
  const RtlirNodeAttributes* attrs = nullptr;  // §37.83: its operators'.
};

// §37.46: the names `expr` reads, wherever they stand in it, appended to
// `out`: an assignment's right side, or a select's index. A member access
// reads its prefix; the member is no name of the scope.
void CollectReads(const Expr* expr, std::vector<std::string_view>& out);

// §11.2.1: the value of `expr`, an index, a bound, a width or a count, where
// it is an elaboration-time constant, folded from the values of the names it
// reads -- parameters and spec params, which the objects those names resolve
// to hold, and genvars; none where it reads a name of anything else, a net or
// a variable among them, whose value only the run fixes.
std::optional<int64_t> ElaborationConstant(const Expr* expr,
                                           const AssignBuild& build);

// The value of `expr` where the source wrote it, in the instance and the
// generate blocks `build` stands in, read at its own width.
Logic4Vec ValueWhereWritten(const Expr* expr, const AssignBuild& build);

// §11.2.1: the value of `constant`, an expression a clause makes a constant
// expression, such as a select's bound or width or a replication's count
// (§11.5.1, §11.4.12.1) or a size cast's width (§6.24.1): its fold, where
// ElaborationConstant folds it, and otherwise its value where the source wrote
// it (ValueWhereWritten), as for $bits of a variable (§20.6.2), an array query
// (§20.7) or a constant function call (§13.4.3), all constants §11.2.1 admits.
int64_t ConstantWhereWritten(const Expr* constant, const AssignBuild& build);

// §37.58 and §37.59: the expression object `expr` stands for, built with
// `build`; null for a kind of expression not modelled.
VpiObject* ExpressionObject(const Expr* expr, const AssignBuild& build);

// §37.59 details 3 and 5: `op`, the cast operation `cast` stands as, built
// with `build`, related to the typespec of the type it casts to - a built-in
// type a keyword names, a typedef or type parameter the scopes around the cast,
// the packages its module imports or the compilation unit declare, or one a
// package declares where the cast names it through the package; or for a
// size, signing or const cast (§6.24.1) one made from its operand's type, a
// size cast's being as wide as the constant it is written with. Answers `op`.
VpiObject* VpiTypedCast(VpiObject* op, const Expr& cast,
                        const AssignBuild& build);

// §37.59: gives `obj`, an operation, a part select or an indexed part select
// built with `build` for `expr` and given no size, its self-determined width
// (§11.6.1), read off its operands' sizes and the constants `expr` writes its
// range or count with; any other expression is left as it is.
void VpiSizeExpression(VpiObject* obj, const Expr& expr,
                       const AssignBuild& build);

// The expression object `expr` stands for, assigned to `target`, whose
// members or elements order a keyed pattern's expressions (§37.59 detail 6).
VpiObject* AssignedExpressionObject(const Expr* expr, const VpiObject* target,
                                    const AssignBuild& build);

}  // namespace delta
