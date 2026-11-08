#include <string_view>

#include "elaborator/elaborator.h"
#include "parser/ast_design.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_type.h"

namespace delta {

static std::string_view AccessedMember(const Expr* e) {
  if (e->rhs && e->rhs->kind == ExprKind::kIdentifier) return e->rhs->text;
  return e->text;
}

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
