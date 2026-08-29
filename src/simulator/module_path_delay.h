#pragma once

// §30.4's module path delays, as they reach the running simulation.
//
// A specify block declares a delay from a module input to a module output, and
// §30.5 says that delay governs when the output transitions. Nothing else in
// the design states it: the output is driven by ordinary logic, and the module
// path only says how long that logic's answer takes to appear. So a module path
// delay is applied where the driver of the path output would otherwise commit
// its value, and §30.6 settles the two against each other -- "the larger of the
// two delays for each path shall be used" -- rather than adding them.
//
// The delay brings §30.7 with it. Two consecutive transitions scheduled on the
// path output closer together in time than the delay are a pulse, and the
// reject and error limits belonging to the delay that forms the pulse's
// trailing edge decide its fate: a pulse at or above the error limit
// propagates, one at or above the reject limit is filtered to x, and one below
// the reject limit is rejected and no pulse emerges. ClassifyPulse in
// simulator/specify_path_delay.h is the function that answers which, and
// RunModulePathTransition below is what carries the answer out.

#include <cstdint>
#include <functional>
#include <string_view>
#include <vector>

#include "common/types.h"
#include "simulator/exec_task.h"

namespace delta {

class Arena;
class SimContext;
class SpecifyManager;
struct Expr;

// Table 30-2's transition slot for a change from `from` to `to`, which is the
// index into PathDelay::delays, PathDelay::reject_limit and
// PathDelay::error_limit that governs that change. The twelve slots run 0 -> 1,
// 1 -> 0, 0 -> z, z -> 1, 1 -> z, z -> 0, 0 -> x, x -> 1, 1 -> x, x -> 0,
// x -> z, z -> x, in that order.
//
// A vector is reduced to one of the four levels the table names before the slot
// is chosen: all bits at z is z, any unknown bit is x, any nonzero value is 1,
// and the rest is 0. `from` equal to `to` is not a transition and answers slot
// 0, the same slot SelectScalarContAssignDelay in
// simulator/lowerer_contassign.cpp gives an unchanged value.
uint8_t ModulePathTransitionSlot(const Logic4Vec& from, const Logic4Vec& to);

// What a module path contributes to one transition of a module path output.
// `found` is false when no registered module path reaches that output from any
// of the sources offered, and the other three members then say nothing: the
// caller keeps whatever delay the driver already had.
struct ModulePathDelay {
  bool found = false;
  uint64_t delay = 0;
  uint64_t reject_limit = 0;
  uint64_t error_limit = 0;
};

// Whether any module path registered in `mgr` names `output` as its
// destination. A driver whose target is named by no module path is left exactly
// as it was, so this is the test that keeps a design with no specify block off
// the module path route altogether.
//
// `output` is the destination as the whole design names it: the port name the
// specify block wrote, under the instance prefix of the module that declared
// the path. Two instances of one cell declare a path to the same `y` and this
// is what tells `u1.y` from `u2.y`; issue #3383 is the case where they could
// not be told apart.
bool IsModulePathOutput(const SpecifyManager& mgr, std::string_view output);

// Everything RunModulePathTransition needs from the driver it delays: the
// context and arena it evaluates in, the manager holding the registered paths,
// the instance-qualified name of the path output, the driver's operands (which
// are the path
// sources it may be reached from, and the signals an inertial wait is
// interrupted by), the expression it re-evaluates when one of those moves, the
// target's bit width, the delay the driver already carried (§30.6's distributed
// delay, zero where the driver had none), and the callback that actually drives
// the target.
struct ModulePathDrive {
  SimContext& ctx;
  Arena& arena;
  const SpecifyManager& mgr;
  std::string_view output;
  const std::vector<std::string_view>& sources;
  const Expr* rhs;
  uint32_t width;
  uint64_t distributed_ticks;
  std::function<void(const Logic4Vec&)> commit;
};

// The module path delay governing `drive.output` transitioning from `from` to
// `to`, selected over the paths that reach that output from one of
// `drive.sources`.
//
// §30.5.3 selects in two steps: "Active specify paths are those whose input has
// transitioned most recently in time", and then "a delay shall be selected from
// among them ... by comparing the correct delay for the specific transition
// being scheduled from each specify path and choosing the smallest".
// SelectActivePath in simulator/specify_path_delay.h is both steps; what is
// gathered here is the candidate list it works on, whose transition times come
// from Variable::last_change_ticks on each path's source.
//
// Every candidate is offered as active in its condition, because the condition
// of a state-dependent path (§30.4.4) is held on PathDelay as the source text
// that wrote it and is not evaluated. Issue #3389 covers that; it shows only
// where two paths reach one output and one of them is conditional.
//
// The pulse limits come from the same path and the same slot as the delay, so a
// caller measuring a pulse against them is measuring it against the limits of
// the delay it selected -- which is what §30.7 asks for and why the selection
// answers with a path rather than with a number.
ModulePathDelay SelectModulePathDelay(const ModulePathDrive& drive,
                                      const Logic4Vec& from,
                                      const Logic4Vec& to);

// Arms, on the source terminal of every module path registered in `mgr`, the
// watcher that records Variable::last_change_ticks. Called once after the
// specify blocks are registered and before the run starts, because §30.5.3
// cannot ask which input transitioned most recently unless something has been
// writing that down since time zero.
//
// A design that declared no module path arms nothing, which leaves
// last_change_ticks at 0 on every variable in it.
void WatchModulePathSources(const SpecifyManager& mgr, SimContext& ctx);

// Waits out one pending transition of a module path output and applies §30.7's
// pulse filtering to whatever the wait turns up.
//
// `old_val` is the value already on the output and `val` the value the driver
// wants to place there; the two differ, or there is no transition to delay.
// `val` is a reference because re-evaluating the driver may replace it, exactly
// as the inertial wait of §28 replaces it.
//
// `*committed` is set when this call has already driven the output, which
// happens for the two pulses that reach it: a propagating pulse drives both of
// its edges and a filtered one drives x and then the trailing value. The caller
// must not commit again after that. `*committed` is left alone otherwise, and
// the caller commits `val` as it would for any other delay.
ExecTask RunModulePathTransition(const ModulePathDrive& drive,
                                 const Logic4Vec& old_val, Logic4Vec& val,
                                 bool* committed);

}  // namespace delta
