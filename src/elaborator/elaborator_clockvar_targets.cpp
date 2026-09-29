#include <string_view>

#include "elaborator/elaborator.h"
#include "parser/ast_design.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_type.h"

// §14.16's synchronous drive target: whether an assignment's left-hand side is
// a writable clockvar, which is what makes a leading cycle delay legal on it
// (§14.11) and a procedural continuous assignment to it illegal. Kept apart
// from elaborator_validate_clocking.cpp, which stood at the size the
// assert-no-oversized-source-files job fails at.

namespace delta {

// The member a member access `e` names, `sig` of `cb.sig`, held in its rhs or,
// where the parser kept it there, in the access's own text.
static std::string_view AccessedMember(const Expr* e) {
  if (e->rhs && e->rhs->kind == ExprKind::kIdentifier) return e->rhs->text;
  return e->text;
}

// Whether `block` declares an output or inout clockvar named `member`.
static bool DeclaresWritableClockvar(const ModuleItem* block,
                                     std::string_view member) {
  for (const auto& sig : block->clocking_signals) {
    if (sig.name == member && (sig.direction == Direction::kOutput ||
                               sig.direction == Direction::kInout)) {
      return true;
    }
  }
  return false;
}

// Whether the interface `ifc` declares a clocking block named `block` with an
// output or inout clockvar named `member`.
static bool InterfaceDeclaresWritableClockvar(const ModuleDecl* ifc,
                                              std::string_view block,
                                              std::string_view member) {
  for (const ModuleItem* item : ifc->items) {
    if (item->kind == ModuleItemKind::kClockingBlock && item->name == block &&
        DeclaresWritableClockvar(item, member)) {
      return true;
    }
  }
  return false;
}

// §25.5.5 and §25.9.1 (printed pages 791-792 and 803): an interface's clocking
// block is reached through a path to the interface instance -- the instance's
// name, an interface port, or a virtual interface, `b1.sb.c` and `v.sb.c` --
// and a drive through it is a synchronous drive as one written in the
// interface is. The path's head is resolved at run time, so what is asked here
// is whether any interface of the design declares a clocking block of that name
// whose clockvar of that name is written. Asked of the module's own blocks
// alone, the drive's `##1` was reported as an illegal intra-assignment delay.
static bool InterfaceClockvarIsWritable(const CompilationUnit* unit,
                                        std::string_view block,
                                        std::string_view member) {
  for (const ModuleDecl* ifc : unit->interfaces) {
    if (InterfaceDeclaresWritableClockvar(ifc, block, member)) return true;
  }
  return false;
}

bool Elaborator::ExprTargetsWritableClockvar(const Expr* e) const {
  while (e != nullptr && e->kind == ExprKind::kSelect) e = e->base;
  if (e == nullptr || e->kind != ExprKind::kMemberAccess || e->lhs == nullptr)
    return false;
  std::string_view member = AccessedMember(e);
  if (member.empty()) return false;
  if (e->lhs->kind == ExprKind::kMemberAccess) {
    return unit_ != nullptr &&
           InterfaceClockvarIsWritable(unit_, AccessedMember(e->lhs), member);
  }
  if (e->lhs->kind != ExprKind::kIdentifier) return false;
  auto block_it = clocking_signals_.find(e->lhs->text);
  if (block_it == clocking_signals_.end()) return false;
  auto sig_it = block_it->second.find(member);
  if (sig_it == block_it->second.end()) return false;
  return sig_it->second.direction == Direction::kOutput ||
         sig_it->second.direction == Direction::kInout;
}

}  // namespace delta
