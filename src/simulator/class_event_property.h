#pragma once

#include <string_view>

namespace delta {

struct Expr;
struct Logic4Vec;
struct Variable;
class SimContext;
class Arena;

// §6.17 with §8.5 and §8.9 (printed pages 117, 183 and 186): the event a
// class's event property holds, where `expr` names one -- a bare name inside
// a method of the class, the running object's property or the running
// class's static one; `h.ev` through a handle, any handle path or an element
// of an array of handles, UVM's `m_events[obj].all_dropped`; or `C::ev` for a
// static property. Each object's property is an event of its own, a static
// one the class's, made on the first reference (ClassObject::event_properties
// and ClassTypeInfo::static_event_properties). A trigger (§15.5.1) sets it
// and an event control (§9.4.2) waits on it as on a declared event. Null
// where `expr` names no event property of a class.
Variable* ClassEventVariable(const Expr* expr, SimContext& ctx, Arena& arena);

// §15.5 with §7.4 and §7.8: the event an element of an array of events names,
// `arr[1]` of `event arr[2]` or `m["k"]` of `event m[string]`. A fixed-size
// array's element is the variable its declaration made (CreateArrayElements);
// an associative array's is made on the first reference under the key the
// index spells, one event for each key, which every trigger and wait of that
// key then reaches. A queue of events holds each event by its identity
// (EventIdentityOf), and its element is that event. Null where `expr` is no
// select of an array of events. Resolved by no name, `-> arr[1]` triggered
// nothing and `@arr[1]` waited for a change of value.
Variable* EventArrayElement(const Expr* expr, SimContext& ctx, Arena& arena);

// §15.5 with §7.10: the value an event `expr` is held by as an element of a
// queue of events, its identity (DeclaredNameTables::RegisterEventIdentity),
// 64 bits wide; 0, the null event, where `expr` names none.
Logic4Vec EventIdentityOf(const Expr* expr, SimContext& ctx, Arena& arena);

// §15.5.1 (printed page 378): the event a trigger's target `expr` names: the
// declared event its resolved `name` finds, else the class event property
// ClassEventVariable finds, `-> h.ev` or `-> ev` in a method, which no name
// does, else the element of an array of events EventArrayElement finds. Null
// where the target names none of them.
Variable* TriggerTargetEvent(const Expr* expr, std::string_view name,
                             SimContext& ctx);

// §15.5.3 (printed page 379) with §6.17: `triggered` on a class's event
// property -- `e.triggered` in a method of the class, `h.e.triggered` or
// `h.e.triggered()` through a handle -- is 1 in the time step a trigger of
// that event (ExecEventTriggerImpl, which marks the event itself) ran, and 0
// for a null event or in any other step. False, `out` untouched, where `expr`
// is no such read. Found by no name, the read answered 0 in the very step of
// the trigger.
bool TryClassEventTriggered(const Expr* expr, SimContext& ctx, Arena& arena,
                            Logic4Vec& out);

}  // namespace delta
