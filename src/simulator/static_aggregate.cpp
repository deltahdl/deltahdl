#include "simulator/static_aggregate.h"

#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "common/arena.h"
#include "simulator/process.h"
#include "simulator/scope.h"
#include "simulator/sim_context.h"
#include "simulator/sim_context_types.h"

namespace delta {

// The name the kept storage stands under outside every frame: one no source
// text can spell, since `$static` is no system name, per instance, since
// §13.3.2 gives static subroutines in different instances separate storage,
// and per subroutine and item. The tables keep the view they are given, so
// the name is interned in the arena where storage is first made under it,
// and only there: a static subroutine may be called any number of times.
static std::string KeptName(std::string_view frame, std::string_view name,
                            SimContext& ctx) {
  std::string key = "$static:";
  if (const Process* proc = ctx.CurrentProcess()) key += proc->inst_prefix;
  key += frame;
  key += '.';
  key += name;
  return key;
}

// Runs `use` on the top frame with the stack taken off the context, so what
// SimContext creates or finds meanwhile is its own, outside every frame.
template <typename Use>
static void WithTopFrameOff(SimContext& ctx, Use use) {
  std::vector<Scope> stack = ctx.SwapScopeStack({});
  if (!stack.empty()) use(stack.back());
  ctx.SwapScopeStack(std::move(stack));
}

// The storage kept under `kept_name` for each kind the frame holds under
// `name`, made on the first call and given the frame's contents on each,
// the frame then referring to it. `intern` gives the name a lasting view
// where storage is first made under it.
template <typename Intern>
static void KeepQueue(Scope& top, std::string_view name,
                      std::string_view kept_name, SimContext& ctx,
                      Intern intern) {
  auto it = top.queues.find(name);
  if (it == top.queues.end()) return;
  QueueObject* kept = ctx.FindQueue(kept_name);
  if (kept == nullptr) kept = ctx.CreateQueue(intern(), 32, -1, true);
  if (kept != it->second) *kept = *it->second;
  it->second = kept;
}

template <typename Intern>
static void KeepAssocArray(Scope& top, std::string_view name,
                           std::string_view kept_name, SimContext& ctx,
                           Intern intern) {
  auto it = top.assoc_arrays.find(name);
  if (it == top.assoc_arrays.end()) return;
  AssocArrayObject* kept = ctx.FindAssocArray(kept_name);
  if (kept == nullptr) kept = ctx.CreateAssocArray(intern(), 32, false);
  if (kept != it->second) *kept = *it->second;
  it->second = kept;
}

template <typename Intern>
static void KeepShape(Scope& top, std::string_view name,
                      std::string_view kept_name, SimContext& ctx,
                      Intern intern) {
  auto it = top.arrays.find(name);
  if (it == top.arrays.end()) return;
  ArrayInfo* kept = ctx.FindArrayInfo(kept_name);
  if (kept == nullptr) {
    ctx.RegisterArray(intern(), *it->second);
    kept = ctx.FindArrayInfo(kept_name);
  } else if (kept != it->second) {
    *kept = *it->second;
  }
  it->second = kept;
}

void RetainStaticAggregate(std::string_view frame, std::string_view name,
                           SimContext& ctx, Arena& arena) {
  std::string kept_name = KeptName(frame, name, ctx);
  auto intern = [&]() -> std::string_view {
    return *arena.Create<std::string>(kept_name);
  };
  WithTopFrameOff(ctx, [&](Scope& top) {
    KeepQueue(top, name, kept_name, ctx, intern);
    KeepAssocArray(top, name, kept_name, ctx, intern);
    KeepShape(top, name, kept_name, ctx, intern);
  });
}

bool RestoreStaticAggregate(std::string_view frame, std::string_view name,
                            SimContext& ctx) {
  std::string kept_name = KeptName(frame, name, ctx);
  bool kept_any = false;
  WithTopFrameOff(ctx, [&](Scope& top) {
    if (QueueObject* kept = ctx.FindQueue(kept_name)) {
      top.queues[name] = kept;
      kept_any = true;
    }
    if (AssocArrayObject* kept = ctx.FindAssocArray(kept_name)) {
      top.assoc_arrays[name] = kept;
      kept_any = true;
    }
    if (ArrayInfo* kept = ctx.FindArrayInfo(kept_name)) {
      top.arrays[name] = kept;
      kept_any = true;
    }
  });
  return kept_any;
}

}  // namespace delta
