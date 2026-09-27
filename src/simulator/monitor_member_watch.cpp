#include "simulator/monitor_member_watch.h"

#include <cstdint>
#include <functional>
#include <memory>
#include <string>
#include <string_view>

#include "common/types.h"
#include "parser/ast_expr.h"
#include "simulator/awaiters_event_control.h"
#include "simulator/class_object.h"
#include "simulator/sim_context.h"

namespace delta {

namespace {

bool SameBits(const Logic4Vec& a, const Logic4Vec& b) {
  if (a.width != b.width || a.nwords != b.nwords) return false;
  for (uint32_t i = 0; i < a.nwords; ++i) {
    if (a.words[i].aval != b.words[i].aval ||
        a.words[i].bval != b.words[i].bval)
      return false;
  }
  return true;
}

// Whether `cur` differs from the value `last` holds, recording it if so.
bool TookNewValue(const Logic4Vec& cur, Logic4Snapshot& last) {
  if (SameBits(cur, last.Get())) return false;
  last.Capture(cur);
  return true;
}

void WatchStaticProperty(const ClassTypeInfo* cls, std::string_view member,
                         const std::function<bool()>& changed) {
  auto last = std::make_shared<Logic4Snapshot>();
  last->Capture(cls->static_properties.at(std::string(member)));
  cls->AddStaticWatcher([cls, member, last, changed]() {
    auto it = cls->static_properties.find(std::string(member));
    if (it == cls->static_properties.end()) return true;
    return TookNewValue(it->second, *last) && changed();
  });
}

// The object is held by its handle, as an event control's watcher holds it,
// since the collector of §8.4 may sweep it while the monitor still lives.
void WatchObjectProperty(uint64_t handle, std::string_view member,
                         SimContext& ctx,
                         const std::function<bool()>& changed) {
  auto last = std::make_shared<Logic4Snapshot>();
  ClassObject* obj = ctx.GetClassObject(handle);
  last->Capture(obj->GetProperty(member, ctx.GetArena()));
  obj->AddWatcher([handle, member, last, changed, &ctx]() {
    const ClassObject* o = ctx.GetClassObject(handle);
    if (o == nullptr) return true;
    return TookNewValue(o->GetProperty(member, ctx.GetArena()), *last) &&
           changed();
  });
}

// Arms on the property `e` names, answering whether it names one.
bool WatchNamedProperty(const Expr* e, SimContext& ctx,
                        const std::function<bool()>& changed) {
  if (e->kind != ExprKind::kIdentifier && e->kind != ExprKind::kMemberAccess)
    return false;
  std::string_view member;
  if (const ClassTypeInfo* cls = ResolveStaticPropertyClass(e, ctx, member)) {
    WatchStaticProperty(cls, member, changed);
    return true;
  }
  uint64_t handle = ResolveMemberObjectHandle(e, ctx, member);
  if (handle == kNullClassHandle) return false;
  WatchObjectProperty(handle, member, ctx, changed);
  return true;
}

}  // namespace

void WatchClassMembersRead(const Expr* expr, SimContext& ctx,
                           const std::function<bool()>& changed) {
  if (expr == nullptr) return;
  if (WatchNamedProperty(expr, ctx, changed)) return;
  if (expr->kind == ExprKind::kMemberAccess) return;
  for (const Expr* sub :
       {expr->lhs, expr->rhs, expr->condition, expr->true_expr,
        expr->false_expr, expr->base, expr->index}) {
    WatchClassMembersRead(sub, ctx, changed);
  }
  for (const Expr* a : expr->args) WatchClassMembersRead(a, ctx, changed);
  for (const Expr* el : expr->elements) WatchClassMembersRead(el, ctx, changed);
}

}  // namespace delta
