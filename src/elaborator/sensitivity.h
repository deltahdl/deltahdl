#pragma once

#include <functional>
#include <string>
#include <string_view>
#include <unordered_map>
#include <unordered_set>
#include <vector>

namespace delta {

struct Expr;
struct Stmt;
struct EventExpr;
struct ModuleItem;
struct ModuleDecl;
struct CompilationUnit;
class Arena;

using FuncMap = std::unordered_map<std::string_view, const ModuleItem*>;

// §9.2.2.2.1: the functions an always_comb or always_latch may call, under the
// keys its calls spell, a bare "f", a package's "p::f", a class's static
// "C::f" or "p::C::f", an instance's "s.t.f" (AddScopedCallFunctions). Each
// class whose static methods `funcs` holds is listed in `class_names` under
// the scope prefix its keys carry, "C::" or "p::C::", with every property the
// class and the classes it extends declare.
struct InferenceFuncs {
  FuncMap funcs;
  std::unordered_map<std::string_view, std::unordered_set<std::string_view>>
      class_names;
};

void CollectExprReads(const Expr* expr, std::unordered_set<std::string>& out);

// The expressions a statement reads, in the positions §9.2.2.2.1's inferred
// sensitivity list takes them from, handed over one at a time. CollectStmtReads
// below is this walk with the names collected off each expression, and a caller
// that needs the expressions themselves asks this instead of restating the
// positions: §25.9's ban on a virtual interface component in a sensitivity list
// is one, `vif.a` having become the two bare identifiers `vif` and `a` by the
// time the names exist, and a check that walked more positions than the
// inference does would reject a component the list never carries.
//
// `fn` is called with a null expression where a position is absent, so a caller
// that reads the expression handles null as CollectExprReads does.
void ForEachStmtReadExpr(const Stmt* stmt,
                         const std::function<void(const Expr*)>& fn);

void CollectStmtReads(const Stmt* stmt, std::unordered_set<std::string>& out);

void CollectWrittenNames(const Stmt* stmt,
                         std::unordered_set<std::string>& out);

// §9.2.2.2.1: the implicit sensitivity list expands the longest static prefix
// of each *net or variable* identifier or select expression read by the
// process. `const_names`, when supplied, names the identifiers that are
// elaboration-time constants (parameters, localparams, specparams) rather than
// nets or variables; a read of such a name -- whether a direct operand or a
// constant select index -- is excluded from the list, since a constant can
// never change to trigger the process.
std::vector<EventExpr> InferSensitivity(
    const Stmt* body, Arena& arena, const InferenceFuncs* calls = nullptr,
    bool exclude_written = true,
    const std::unordered_set<std::string_view>* const_names = nullptr);

// Where the block whose calls AddScopedCallFunctions resolves stands: the
// module declarations being elaborated, outermost first and the block's own
// last, the compilation unit, and the lookup of the module an instance names.
struct ScopedCallSite {
  const std::vector<const ModuleDecl*>& decl_path;
  const CompilationUnit& unit;
  const std::function<const ModuleDecl*(std::string_view)>& find_module;
};

// §9.2.2.2.1 with §8.23, §23.6, §23.8 and §26.3: enters in `calls` every
// function `body` calls, directly or through the functions it calls, by a
// scoped name `calls` does not yet hold, under the key the call spells: a
// static method of a class a module of the chain, a package or the
// compilation unit declares, "C::f" or "p::C::f", and a function a dotted
// path reaches, searched from the block's module and then from each module
// enclosing it, its first step an instance of that module or the module's own
// name. Only the inference reads the result; the elaborator's own function
// table stays as it is for every other rule.
void AddScopedCallFunctions(const Stmt* body, const ScopedCallSite& site,
                            Arena& arena, InferenceFuncs& calls);

}  // namespace delta
