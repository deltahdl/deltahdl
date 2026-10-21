#pragma once

#include <cstddef>
#include <functional>
#include <string_view>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "parser/ast_type.h"

namespace delta {

struct EventExpr;
struct Expr;
struct ModuleDecl;
struct ModuleItem;
struct PropertyExprNode;
struct SeqLinearBody;
struct SeqMatchAssign;
struct Stmt;

using NamedDecls = std::unordered_map<std::string_view, const ModuleItem*>;

// The walks the rules of Clause 16 on a module's sequences, properties and
// concurrent assertions share, each handing `fn` what it reaches in source
// order and skipping what is absent.

// Each statement of the procedure or the subroutine `item`, the statements
// nested in them among them; none for any other item.
void ForEachProceduralStmt(const ModuleItem* item,
                           const std::function<void(const Stmt*)>& fn);

// Each concurrent assertion statement of the module `decl`, at module level
// or in a procedure or a subroutine.
void ForEachConcurrentAssertion(const ModuleDecl* decl,
                                const std::function<void(const Stmt*)>& fn);

// The named sequences the module `decl` declares, and its named properties
// where `with_properties`, by name.
NamedDecls NamedDeclsByName(const ModuleDecl* decl, bool with_properties);

// `e` and each expression under it.
void ForEachSubExpr(const Expr* e, const std::function<void(const Expr*)>& fn);

// Whether `e` or an expression under it answers `pred`.
bool AnySubExpr(const Expr* e, const std::function<bool(const Expr*)>& pred);

// `body` and each body nested in it: the operands of an intersect, an `and`
// and a top-level `or`.
void ForEachBody(const SeqLinearBody& body,
                 const std::function<void(const SeqLinearBody&)>& fn);

// Each expression written in `body` or a body nested in it: its operands,
// the right-hand sides and calls of its match items and first_match's, and
// its throughout conditions.
void ForEachBodyExpr(const SeqLinearBody& body,
                     const std::function<void(const Expr*)>& fn);

// `node` and each property node under it.
void ForEachTreeNode(const PropertyExprNode* node,
                     const std::function<void(const PropertyExprNode&)>& fn);

// Each expression written in the property tree under `node`: each node's
// boolean, and the expressions of the sequences it holds.
void ForEachTreeExpr(const PropertyExprNode* node,
                     const std::function<void(const Expr*)>& fn);

// The declaration in `decls` that `e` instantiates, written as a call or as
// a bare name; null where it names none.
const ModuleItem* InstantiatedDecl(const Expr* e, const NamedDecls& decls);

// Whether `e` is the identifier `name`; false where `e` is absent.
bool IsNameRef(const Expr* e, std::string_view name);

// Whether `e` is, in its entirety, a reference to one of `locals`.
bool IsLocalRef(const Expr* e,
                const std::unordered_set<std::string_view>& locals);

// Whether operand `i` of `body` is repeated from zero, so has a match that
// assigns nothing its match items assign.
bool RepeatedFromZero(const SeqLinearBody& body, size_t i);

// §16.13.5 and §16.13.6: the sequence method, `triggered` or `matched`, `e`
// applies, empty where it applies none.
std::string_view SequenceMethodOf(const Expr* e);

// §16.8.2: the direction of each formal of `seq` declared a local variable
// formal argument, input where none is written; kNone for any other formal.
std::vector<Direction> LocalFormalDirections(const ModuleItem* seq);

// Whether the signal or the iff condition of one of `events` names one of
// `names`.
bool EventsMention(const std::vector<EventExpr>& events,
                   const std::unordered_set<std::string_view>& names);

// §16.8.2: whether a local variable formal argument of direction `dir` gives
// its actual a value, an inout or an output one.
bool IsOutward(Direction dir);

// Whether one of `items` assigns `name`.
bool ItemsAssign(const std::vector<SeqMatchAssign>& items,
                 std::string_view name);

// Whether a match item of `body`, of a body nested in it or of its
// first_match assigns `name`.
bool BodyAssigns(const SeqLinearBody& body, std::string_view name);

// §16.8 and §17.3: the references to a formal in a body: all of them, and
// those a `$` actual may reach, the upper bound of a cycle delay or a
// repetition range and an actual argument of an instance written whole.
struct FormalReferences {
  int all = 0;
  int permitted = 0;
};

// Adds the references to `name` in `e` to `refs`, the arguments of the calls
// it holds that are `name` alone as permitted ones.
void CountFormalInExpr(const Expr* e, std::string_view name,
                       FormalReferences& refs);

// Adds the references to `name` in `body` and the bodies nested in it to
// `refs`, its delay and repetition bounds among them, `##d` and `[*d]`
// standing for the range [d:d], whose lower bound d is.
void CountFormalInBody(const SeqLinearBody& body, std::string_view name,
                       FormalReferences& refs);

// Adds the references to `name` in the property tree under `node` to `refs`.
void CountFormalInTree(const PropertyExprNode* node, std::string_view name,
                       FormalReferences& refs);

}  // namespace delta
