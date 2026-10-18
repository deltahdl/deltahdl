#pragma once

#include <functional>
#include <string>
#include <string_view>
#include <unordered_map>
#include <vector>

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

// §37.58 and §37.59: the expression object `expr` stands for, built with
// `build`; null for a kind of expression not modelled.
VpiObject* ExpressionObject(const Expr* expr, const AssignBuild& build);

// The expression object `expr` stands for, assigned to `target`, whose
// members or elements order a keyed pattern's expressions (§37.59 detail 6).
VpiObject* AssignedExpressionObject(const Expr* expr, const VpiObject* target,
                                    const AssignBuild& build);

}  // namespace delta
