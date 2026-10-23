#pragma once

#include <span>
#include <string>
#include <string_view>
#include <vector>

#include "elaborator/rtlir.h"
#include "elaborator/rtlir_scopes.h"
#include "parser/ast_stmt.h"
#include "simulator/vpi_design_attach_build.h"
#include "simulator/vpi_object.h"

// Shared between vpi_design_attach_procedures.cpp, which walks a procedure's
// statements into the VPI model, vpi_design_attach_calls.cpp, which resolves
// what a call statement calls and what a foreach loop indexes, and
// vpi_design_attach_call_lookup.cpp, which finds the classes and the block
// variables it resolves them against.

namespace delta {

struct ClassDecl;
struct DataType;
struct Expr;
struct ModuleItem;

// Where the objects a statement holds hang: the scope object around it, and
// the path a named one among them is named under, which an unnamed scope
// between them leaves as it was. A scope a block stands as also carries the
// block, whose declarations a name the statement writes resolves to first
// (§9.3, §23.9), and every scope carries the one around it, null at a
// procedure's own scope. The body of a sequence or a property declaration
// also carries the object holding the stand-ins for its formals
// (VpiFormalNames), whose names a name finds first (§16.8, §16.12).
struct BlockParent {
  VpiObject* scope;
  const std::string& path;
  const Stmt* block = nullptr;
  const BlockParent* outer = nullptr;
  const VpiObject* formals = nullptr;
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
  // §26.2: the package a call held outside every procedure stands in, empty
  // for none (VpiCallStand).
  std::string_view package = {};
};

// §37.42: what a call statement stands as. `type` is the kind of tf call, zero
// for a statement that calls nothing the walk resolves; `name` is the
// subroutine it calls; `prefix` is the object a method is applied to (detail
// 2), or the class var a chain of `prefix_members` starts from;
// `user_defined` is the figure's vpiUserDefn; `systf` is the systf object
// a call of a registered system task reaches; `called` is the task or
// function object of the declaration a task, function or method call calls;
// and `sysfunctype` is the kind of value a registered system function returns.
struct CallShape {
  int type = 0;
  std::string_view name;
  VpiObject* prefix = nullptr;
  std::vector<std::string_view> prefix_members = {};
  bool user_defined = false;
  VpiObject* systf = nullptr;
  VpiObject* called = nullptr;
  int sysfunctype = 0;
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

// §18.7 with §8.4: the class defn of the class of the value the method call
// whose callee is `access`, a member access, is applied through, as the scope
// `parent` stands in reads it; null where it reads no class the design
// declares.
VpiObject* MethodCallClassDefn(const Expr& access, const BlockParent& parent,
                               const BodyWalk& walk);

// §37.42: make `made` the tf call the call `call`, written in an expression
// standing in `parent`, is, as a call statement written there is made; false,
// leaving `made` alone, where the call calls nothing the walk resolves.
bool ShapeExprCall(const Expr& call, VpiObject* made, const BlockParent& parent,
                   const BodyWalk& walk);

// A class declaration with the flat name of the scope its class defn was made
// under, the key VpiClassDefnObjects files the defn by: the instance's prefix,
// a package's name or "$unit".
struct VpiScopedClass {
  const ClassDecl* decl = nullptr;
  std::string scope;
};

// §6.18 with §8.3: the class name `name` stands for, the class at the end of
// a typedef's chain of names where it is a typedef name, `typedef B B_t;`.
std::string_view VpiClassNameOf(const BodyWalk& walk, std::string_view name);

// The class the design declares under `name`: in the package `package` where
// one is named (§26.3), and otherwise in the instance's module, the
// compilation unit or a package the module imports the name from, by name or
// with a wildcard (§26.3), a typedef name standing for the class it names. No
// declaration for a name the design declares no class under, a built-in class
// among them.
VpiScopedClass VpiFindClassDecl(const BodyWalk& walk, std::string_view name,
                                std::string_view package = {});

// §8.3: the method `cls` declares under `name`, null for none.
const ModuleItem* VpiMethodNamed(const ClassDecl& cls, std::string_view name);

// A class a step of the walk holds: its name, and the arguments the
// specialization it is held as gives its parameters (§8.25), none for the
// default one.
struct VpiHeldClass {
  std::string_view name;
  std::span<const DataType> args;
};

// §8.13 with §8.25: the class `decl`, held under the specialization `args`,
// extends: the one its extends clause names, with the arguments written
// there, or, where the clause names one of the class's own type parameters,
// class C #(type T = B) extends T, the class the specialization's argument for
// it names, else the parameter's default (§8.25.1).
VpiHeldClass VpiBaseOf(const ClassDecl& decl, std::span<const DataType> args);

// §9.3.4 with §23.6: the declaration of the variable `name` that a block named
// `block`, written in one of the procedures of `mod`, declares, which a
// hierarchical name, block.name, reaches from anywhere in the instance; null
// where no block of the name declares one.
const Stmt* VpiNamedBlockVarDecl(const RtlirModule& mod, std::string_view block,
                                 std::string_view name);

// §37.42 with §37.60: what the expression statement `expr`, standing in the
// scope `parent` stands for, calls. A task is enabled with or without an
// argument list (§13.3), so the callee is the expression itself where no list
// follows it.
CallShape CallShapeOf(const Expr& expr, const BlockParent& parent,
                      const BodyWalk& walk);

}  // namespace delta
