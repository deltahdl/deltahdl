#pragma once

#include <string>
#include <string_view>
#include <vector>

#include "elaborator/rtlir.h"
#include "elaborator/rtlir_scopes.h"
#include "parser/ast_stmt.h"
#include "simulator/vpi_design_attach_build.h"
#include "simulator/vpi_object.h"

// Shared between vpi_design_attach_procedures.cpp, which walks a procedure's
// statements into the VPI model, and vpi_design_attach_calls.cpp, which
// resolves what a call statement calls and what a foreach loop indexes.

namespace delta {

struct DataType;
struct Expr;

// Where the objects a statement holds hang: the scope object around it, and
// the path a named one among them is named under, which an unnamed scope
// between them leaves as it was. A scope a block stands as also carries the
// block, whose declarations a name the statement writes resolves to first
// (§9.3, §23.9), and every scope carries the one around it, null at a
// procedure's own scope.
struct BlockParent {
  VpiObject* scope;
  const std::string& path;
  const Stmt* block = nullptr;
  const BlockParent* outer = nullptr;
};

// What a walk of one procedure body builds with: the design and the instance's
// module, which a call's subroutine is found among; the objects the instance's
// declarations stand as, keyed under its prefix; what a call statement is
// built with; the build; and the process the body runs in (null for an
// assertion the elaborator carries as a process).
struct BodyWalk {
  const RtlirDesign& design;
  const RtlirModule& mod;
  const VpiObjectMap& objects;
  const std::string& prefix;
  const VpiCallBuild& calls;
  const VpiAttachBuild& build;
  VpiObject* process = nullptr;
  // §27.4: the prefixes of the generate block instances the procedure stands
  // in, innermost last, empty for one of the instance itself; each walk of an
  // item sets it before any statement is walked.
  const GenBlockPrefixes* gen_prefixes = nullptr;
};

// §37.42: what a call statement stands as. `type` is the kind of tf call, zero
// for a statement that calls nothing the walk resolves; `name` is the
// subroutine it calls; `prefix` is the object a method is applied to (detail
// 2), or the class var a chain of `prefix_members` starts from;
// `user_defined` is the figure's vpiUserDefn; `systf` is the systf object
// a call of a registered system task reaches; and `called` is the task or
// function object of the declaration a task, function or method call calls.
struct CallShape {
  int type = 0;
  std::string_view name;
  VpiObject* prefix = nullptr;
  std::vector<std::string_view> prefix_members = {};
  bool user_defined = false;
  VpiObject* systf = nullptr;
  VpiObject* called = nullptr;
};

// The items a begin or fork block holds, its declarations among them.
inline const std::vector<Stmt*>& BlockItems(const Stmt& block) {
  return block.kind == StmtKind::kFork ? block.fork_stmts : block.stmts;
}

// Where a statement standing in `parent` is written, as a call it holds
// resolves the subroutine it calls.
VpiCallSite CallSiteOf(const BlockParent& parent, const BodyWalk& walk);

// §37.17: the object kind of a variable declared with `type` in the instance,
// leaving its unpacked dimensions aside.
int TypeVariableKind(const DataType& type, const BodyWalk& walk);

// §23.9: the declaration of the variable `name` a block around the statement
// `parent` stands for declares, the innermost first, with `where` set to the
// block's; null where no block declares one.
const Stmt* BlockVarDecl(const BlockParent& parent, std::string_view name,
                         const BlockParent*& where);

// The plain names a chain of member accesses joins, `a.b.c` as a, b and c,
// appended to `names`; false where a link is anything else.
bool ChainNames(const Expr& expr, std::vector<std::string_view>& names);

// §12.7.3: the kind of the first index variable of a foreach loop over the
// array `array` names, the index type's where the array's first dimension is
// associative and an int var otherwise; an array a block around the
// statement declares is found first (§23.9).
int ForeachIndexKind(const Expr* array, const BlockParent& parent,
                     const BodyWalk& walk);

// §37.42 with §37.60: what the expression statement `expr`, standing in the
// scope `parent` stands for, calls. A task is enabled with or without an
// argument list (§13.3), so the callee is the expression itself where no list
// follows it.
CallShape CallShapeOf(const Expr& expr, const BlockParent& parent,
                      const BodyWalk& walk);

}  // namespace delta
