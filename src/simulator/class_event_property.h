#pragma once

#include <string_view>

namespace delta {

struct Expr;
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

// §15.5.1 (printed page 378): the event a trigger's target `expr` names: the
// declared event its resolved `name` finds, else the class event property
// ClassEventVariable finds, `-> h.ev` or `-> ev` in a method, which no name
// does. Null where the target names neither.
Variable* TriggerTargetEvent(const Expr* expr, std::string_view name,
                             SimContext& ctx);

}  // namespace delta
