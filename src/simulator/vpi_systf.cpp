#include <cctype>
#include <cmath>
#include <cstdarg>
#include <cstddef>
#include <cstdint>
#include <cstdio>
#include <string>
#include <string_view>
#include <vector>

#include "common/arena.h"
#include "common/lexical_limits.h"
#include "common/types.h"
#include "parser/ast.h"
#include "simulator/evaluation.h"
#include "simulator/net.h"
#include "simulator/scheduler.h"
#include "simulator/sim_context.h"
#include "simulator/vpi.h"
// §37.10 detail 3: the package/interface/program instance kinds are defined in
// the SystemVerilog VPI header alongside the §37.10 vpiInstance relation, and
// §37.59's vpiRefObj -- the reference an expression naming a variable is -- is
// there with them.
#include "simulator/sv_vpi_user.h"
#include "simulator/variable.h"
#include "simulator/vpi_internal.h"

namespace delta {

VpiHandle VpiContext::RegisterSystf(VpiSystfData* data) {
  if (!data) return nullptr;

  // §36.9.1: a user-defined system task or system function name shall begin
  // with a dollar sign. §38.37.1 sharpens this: the dollar sign shall be
  // followed by one or more characters that are legal in a SystemVerilog simple
  // identifier. Refuse a name that fails either part of the rule (a missing or
  // bare "$", or any illegal trailing character).
  if (!VpiSystfNameIsValid(data->tfname)) {
    last_error_.state = kVpiPLI;
    last_error_.level = kVpiError;
    last_error_.message =
        "system task or function name must be '$' followed by one or more "
        "identifier characters";
    return nullptr;
  }

  // §38.37.1: of the tfname a registration carries, "the maximum name length
  // shall be the same as for SystemVerilog identifiers", which §5.6 caps at the
  // implementation's own limit and requires an error to be reported for. That
  // limit is kMaxIdentifierLength, the one the lexer measures an identifier
  // against, so the two are the same by construction rather than by agreement
  // between two literals.
  //
  // §36.3's "the name can be any size" governs the name a SystemVerilog source
  // file writes and not this one: that is the token LexSystemIdentifier reads,
  // and this is the string a PLI application hands the registration.
  if (std::string_view(data->tfname).size() > kMaxIdentifierLength) {
    last_error_.state = kVpiPLI;
    last_error_.level = kVpiError;
    // The message names the rule rather than the number, both because
    // VpiErrorInfo::message is a const char* with nowhere to keep a built
    // string and because the rule is that the two maxima agree, not that either
    // is 1024.
    last_error_.message =
        "system task or function name exceeds the maximum identifier length";
    return nullptr;
  }

  // §36.9.1: the registration of system tasks shall occur prior to elaboration
  // or the resolution of references. Once elaboration has begun the window has
  // closed, so reject the registration.
  if (elaboration_started_) {
    last_error_.state = kVpiPLI;
    last_error_.level = kVpiError;
    last_error_.message =
        "system task or function registration must precede elaboration";
    return nullptr;
  }

  systfs_.push_back(*data);

  // §38.37 Returns row: registration produces a handle to the callback
  // object standing in for this system task or system function.
  auto* systf_obj = AllocObject();
  systf_obj->type = kVpiCallback;
  systf_obj->index = static_cast<int>(systfs_.size() - 1);
  // §38.12: mark this callback as a system task/function so
  // vpi_get_systf_info() can tell it apart from a simulation callback and read
  // back its record.
  systf_obj->is_systf = true;
  return systf_obj;
}

const VpiSystfData* VpiContext::ResolveSystf(const char* name) const {
  // §36.3.2: Clause 20 and Clause 21 built-in system tasks/functions, and any
  // tool-specific ones, share the same '$'-prefixed namespace as user-defined
  // names. If a user-provided PLI application is associated (through the PLI
  // mechanism) with the same name as a built-in, that application shall
  // override the built-in, replacing its functionality. The lookup therefore
  // searches the registry first; a matching entry is the overriding application
  // to run. A null result means no registration claimed the name, so the
  // built-in stands.
  if (name == nullptr) return nullptr;

  // Walk newest-first so that when more than one registration shares the name,
  // the most recently registered one wins - a later user application overrides
  // an earlier registration (including a built-in registered ahead of it).
  for (auto it = systfs_.rbegin(); it != systfs_.rend(); ++it) {
    if (it->tfname != nullptr && std::string_view(it->tfname) == name) {
      return &*it;
    }
  }
  return nullptr;
}

namespace {

// §36.4: one task/function argument as the application reaches it. An actual
// that names a variable is carried by that variable itself, so a write through
// vpi_put_value lands where the design will read it and a read sees whatever
// the design last wrote -- the clause asks for both, "PLI routines are provided
// that allow the PLI applications to read and write to the task/function
// arguments". Anything else is an expression rather than a name: its value goes
// into a holder of its own, which reads correctly and which a write cannot
// carry back to a call site with nowhere to put it.
//
// §37.42 detail 8 spells an omitted argument, which a call site writes as an
// empty position, and VpiMakeEmptyArgument is what sets that shape.
//
// `evaluate` is what separates the two periods a call object is built in.
// §36.8.3 has the calltf called "each time the associated user-defined system
// task or system function is executed", so an actual that is an expression has
// a value there and the holder is filled with it. §36.8.2 has the compiletf
// called "when the user-defined system task or system function name is
// encountered during parsing or compiling", where the design has not run: there
// is no value to read, and reading one would mean running the source's own
// functions once per call site before the simulation started, so the holder is
// left empty and the argument stands for what the source wrote rather than for
// what it will produce.
VpiObject* SystfCallArgument(VpiObject* arg, const Expr* actual,
                             SimContext& ctx, Arena& arena, bool evaluate) {
  if (actual == nullptr) {
    VpiMakeEmptyArgument(arg);
    return arg;
  }
  Variable* named = actual->kind == ExprKind::kIdentifier
                        ? ctx.FindVariable(actual->text)
                        : nullptr;
  if (named != nullptr) {
    arg->type = vpiRefObj;
    // Expr::text is a view into the source buffer, which does not end where the
    // identifier does, so the name is copied into the run's arena to be the
    // standalone string VpiObject::name has to hold. Without the copy
    // vpi_get_str(vpiName, arg) reported the rest of the source file.
    arg->name = std::string_view(
        arena.AllocString(actual->text.data(), actual->text.size()),
        actual->text.size());
    arg->var = named;
  } else {
    arg->type = vpiOperation;
    auto* holder = arena.Create<Variable>();
    if (evaluate) holder->value = EvalExpr(actual, ctx, arena);
    arg->var = holder;
  }
  // §37.3.5: "VPI gives applications access to arbitrarily complex expressions
  // from the SystemVerilog source, either as arguments to system tasks or
  // functions (see 36.4) or by traversing the design hierarchy. Expressions may
  // have side effects when evaluated." This is that first way, and
  // VpiObject::has_side_effects is the mark the value, property and relation
  // routines settle the subclause's rules by. No pass wrote it, so no argument
  // an application was ever handed was an expression with side effects and
  // every one of those rules stood over an empty set.
  arg->has_side_effects = VpiSourceExprHasSideEffects(actual);
  arg->size = static_cast<int>(arg->var->value.width);
  return arg;
}

}  // namespace

VpiHandle VpiContext::MakeSystfCallObject(const VpiSystfData& data,
                                          const Expr* call_site,
                                          SimContext& ctx, Arena& arena,
                                          bool evaluate_args) {
  // §37.42: the system task or function call a PLI application is run for,
  // which the application reaches with vpi_handle(vpiSysTfCall, NULL). It is
  // also where a system function's return value is put: vpi_put_value writes
  // through the object's own storage, so the call carries a variable of its own
  // for the application to write and for this routine's caller to read back.
  auto* call = AllocObject();
  call->type = (data.type == vpiSysFunc) ? vpiSysFuncCall : vpiSysTaskCall;
  call->name = data.tfname != nullptr ? std::string_view(data.tfname)
                                      : std::string_view();
  auto* value_holder = arena.Create<Variable>();
  // §36.8.1: "The value returned by the sizetf routine shall be the number of
  // bits that the calltf routine shall provide as the return value for the
  // system function", so the holder the application writes through is that
  // wide. §38.37.1's default is what SystfResultSizeBits answers where no
  // sizetf is provided: "a user-defined system function of type vpiSizedFunc or
  // vpiSizedSignedFunc shall return 32 bits". A sizetf answering with no bits
  // at all describes no value, so the default stands rather than a width
  // nothing can hold.
  int result_bits = SystfResultSizeBits(data);
  auto width = static_cast<uint32_t>(
      result_bits > 0 ? result_bits : kVpiDefaultSizedFuncBits);
  value_holder->value = MakeLogic4VecVal(arena, width, 0);
  call->var = value_holder;
  call->size = static_cast<int>(width);

  // §36.4: the arguments the call site wrote, hung on the call so §37.42's
  // vpiArgument iteration reaches them. They are attached before the routine
  // runs, because the application reads them from inside it.
  if (call_site != nullptr) {
    for (const Expr* actual : call_site->args) {
      call->children.push_back(
          SystfCallArgument(AllocObject(), actual, ctx, arena, evaluate_args));
    }
  }
  return call;
}

bool VpiContext::CallRegisteredSystf(const char* name, const Expr* call_site,
                                     SimContext& ctx, Logic4Vec& result,
                                     Arena& arena) {
  const VpiSystfData* data = ResolveSystf(name);
  if (data == nullptr) return false;

  VpiHandle call = MakeSystfCallObject(*data, call_site, ctx, arena,
                                       /*evaluate_args=*/true);

  // A call reached from inside another PLI application is the inner one while
  // it runs, so the outer call is put back rather than cleared.
  VpiHandle outer_call = CurrentSystfCall();
  SetCurrentSystfCall(call);
  if (data->calltf != nullptr) {
    data->calltf(static_cast<const char*>(data->user_data));
  }
  SetCurrentSystfCall(outer_call);

  result = call->var->value;
  return true;
}

void VpiContext::CallCompiletfForSourceCall(const VpiSystfData& data,
                                            const Expr* call_site,
                                            SimContext& ctx, Arena& arena) {
  // §36.8.2: "Providing a compiletf routine is optional." A registration that
  // supplied none has nothing to call and nothing to call it for, so no call
  // object is stood up either.
  if (data.compiletf == nullptr) return;

  VpiHandle call = MakeSystfCallObject(data, call_site, ctx, arena,
                                       /*evaluate_args=*/false);

  // The same standing-and-restoring the calltf gets, and for the same reason:
  // a compiletf that reaches a PLI routine which itself calls a system task
  // leaves this one to be put back.
  VpiHandle outer_call = CurrentSystfCall();
  SetCurrentSystfCall(call);
  VpiSystfInvoke(data.compiletf, data.user_data);
  SetCurrentSystfCall(outer_call);
}

void VpiContext::GetSystfInfo(VpiHandle obj, VpiSystfData* systf_data_p) {
  // §38.12 / §38.1: the handle and the destination are both mandatory. With no
  // structure to fill, or no callback to read, there is nothing to report.
  if (obj == nullptr || systf_data_p == nullptr) return;

  // §38.12: obj must name a system task or system function callback. Other
  // objects (including simulation callbacks) carry no s_vpi_systf_data record.
  if (obj->type != kVpiCallback || !obj->is_systf) return;
  int idx = obj->index;
  if (idx < 0 || idx >= static_cast<int>(systfs_.size())) return;

  // §38.12: copy the stored registration into the application-owned structure.
  // The routine never allocates that memory; it only writes the fields.
  *systf_data_p = systfs_[idx];
}

void VpiContext::GetCbInfo(VpiHandle obj, VpiCbData* cb_data_p) {
  // §38.8: the destination structure is allocated by the application. With no
  // structure to fill, or no callback to read, there is nothing to report; the
  // routine never allocates that memory itself.
  if (obj == nullptr || cb_data_p == nullptr) return;

  // §38.8: obj must name a simulation-related callback. A system task/function
  // callback carries an s_vpi_systf_data record instead (read it through
  // vpi_get_systf_info), so it is not a valid argument here.
  if (obj->type != kVpiCallback || obj->is_systf) return;
  int idx = obj->index;
  if (idx < 0 || idx >= static_cast<int>(callbacks_.size())) return;

  // §38.8: report the callback's information by writing the stored s_cb_data
  // fields into the caller's structure.
  *cb_data_p = callbacks_[idx];
}

VpiHandle VpiContext::CreateTimeQueue() {
  // §38.13: a time queue object carries no further state of its own; its kind
  // is enough for GetTime() to know to report the next future event time.
  auto* obj = AllocObject();
  obj->type = kVpiTimeQueue;
  return obj;
}

void VpiContext::GetTime(VpiHandle obj, VpiTime* time_p) {
  // §38.13 / §38.1: the destination is mandatory and its memory belongs to the
  // application. With nowhere to write, there is nothing to do; the routine
  // never allocates the structure itself.
  if (time_p == nullptr) return;

  // §38.13: choose the time value and the unit it is expressed in. A time queue
  // object reports the scheduled time of the next future event; every other
  // query reports the current simulation time. Both a null handle and a time
  // queue object are read in the simulation time unit; a regular object is read
  // in its own timescale.
  uint64_t ticks = 0;
  bool use_sim_time_unit = (obj == nullptr);
  if (obj != nullptr && obj->type == kVpiTimeQueue) {
    // §38.13: report the scheduled time of the future event. An object produced
    // by the vpi_iterate(vpiTimeQueue, NULL) walk carries its own slot time, so
    // each iterated slot reports its distinct scheduled time; the generic time
    // queue placeholder instead reads the scheduler's next future event live.
    ticks = obj->has_scheduled_time
                ? obj->time_queue_time
                : (scheduler_ ? scheduler_->NextEventTime().ticks : 0);
    use_sim_time_unit = true;
  } else {
    ticks = scheduler_ ? scheduler_->CurrentTime().ticks : 0;
  }

  // §38.13 (Figure 38-6): the caller's time_p->type selects the form of the
  // result. vpiScaledRealTime asks for a real scaled to the relevant time unit;
  // anything else (vpiSimTime) asks for the raw 64-bit count.
  if (time_p->type == kVpiScaledRealTime) {
    // §38.13: scale the simulation-time-unit count into the target unit - the
    // object's timescale, or the simulation time unit for a null handle or a
    // time queue object. The exponent difference is the power-of-ten conversion
    // between the two units.
    int target_unit = use_sim_time_unit ? sim_time_unit_ : obj->time_unit;
    double scale =
        std::pow(10.0, static_cast<double>(sim_time_unit_ - target_unit));
    time_p->real = static_cast<double>(ticks) * scale;
  } else {
    // §38.13 (Figure 38-6): vpiSimTime delivers the 64-bit simulation time
    // split into its high and low 32-bit halves.
    time_p->high = static_cast<uint32_t>(ticks >> 32);
    time_p->low = static_cast<uint32_t>(ticks & 0xFFFFFFFFu);
  }
}

bool VpiIsPrimitiveType(int type) {
  // §37.35: `primitive` is drawn as a class definition - bold italic letters in
  // a dotted enclosure - holding the gate, switch and udp object definitions,
  // and §37.4.1 makes such an enclosure a grouping rather than an object of its
  // own. So vpiPrimitive is the name of the group and these are the kinds an
  // object grouped by it actually has; §37.36 detail 2's sequential and
  // combinational UDPs are the two forms the udp definition takes.
  switch (type) {
    case vpiGate:
    case vpiSwitch:
    case vpiUdp:
    case vpiSeqPrim:
    case vpiCombPrim:
      return true;
    default:
      return false;
  }
}

// §38.10: the four object categories that carry delays. Their legal
// no_of_delays values differ, so vpi_get_delays() classifies the object first.
bool VpiObjectIsPrimitive(int type) {
  return VpiIsPrimitiveType(type) || type == vpiPrimitive;
}

namespace {

// §38.10 / §38.32: a position-tracking cursor over the delay structure's da[]
// array. The min:typ:max triple and per-delay run helpers all walk one
// VpiDelay::da[] in source order, advancing a shared index `k` and forming each
// entry under one `time_type`. Bundling the three together names that single
// entity - a cursor into the da[] array - rather than threading them apart.
struct DelayCursor {
  VpiDelay* delay_p;  // the application-allocated delay structure being walked
  int k;              // current write/read position within delay_p->da[]
  int time_type;      // the form (vpiScaledRealTime/vpiSimTime/...) of entries
};

// §38.10: whether `n` is a legal number of delays to request for an object of
// `type` that carries `available` stored delays. For a primitive the count is
// 2 or 3; for a module (path-delay) object 1, 2, 3, 6, or 12; for an
// intermodule path 2 or 3; for a timing check it must match the number of
// limits the check actually has. Any other object bears no delays.
bool VpiNoOfDelaysLegal(int type, int n, size_t available) {
  if (VpiObjectIsPrimitive(type)) return n == 2 || n == 3;
  if (type == vpiModPath)
    return n == 1 || n == 2 || n == 3 || n == 6 || n == 12;
  if (type == vpiInterModPath) return n == 2 || n == 3;
  if (type == vpiTchk) return n == static_cast<int>(available);
  return false;
}

// §38.10: write one delay value into a caller-supplied time entry. The form is
// dictated solely by the delay structure's time_type - the entry's own type
// field is ignored on input and overwritten with time_type. vpiScaledRealTime
// delivers a real; vpiSimTime delivers the value as a 64-bit count split across
// high/low; vpiSuppressTime asks for no time and leaves the value cleared.
void VpiWriteDelayValue(VpiTime* slot, int time_type, double value) {
  slot->type = time_type;
  slot->high = 0;
  slot->low = 0;
  slot->real = 0.0;
  if (time_type == vpiScaledRealTime) {
    slot->real = value;
  } else if (time_type == vpiSimTime) {
    auto ticks = static_cast<uint64_t>(value);
    slot->high = static_cast<uint32_t>(ticks >> 32);
    slot->low = static_cast<uint32_t>(ticks & 0xFFFFFFFFu);
  }
}

// §38.32: read one delay value out of a caller-supplied time entry, the inverse
// of VpiWriteDelayValue. The form is dictated by the delay structure's
// time_type: vpiScaledRealTime carries the value in the real field; vpiSimTime
// carries it as a 64-bit count split across high/low; vpiSuppressTime carries
// no time, so the value is zero.
double VpiReadDelayValue(const VpiTime& slot, int time_type) {
  if (time_type == vpiScaledRealTime) return slot.real;
  if (time_type == vpiSimTime) {
    uint64_t ticks = (static_cast<uint64_t>(slot.high) << 32) | slot.low;
    return static_cast<double>(ticks);
  }
  return 0.0;
}

// §38.10 (Table 38-2): emit the min:typ:max triple of one stored delay field
// into da[cur.k..cur.k+2], advancing the cursor past the run.
void VpiWriteMtmTriple(DelayCursor& cur, double min_v, double typ_v,
                       double max_v) {
  VpiWriteDelayValue(&cur.delay_p->da[cur.k++], cur.time_type, min_v);
  VpiWriteDelayValue(&cur.delay_p->da[cur.k++], cur.time_type, typ_v);
  VpiWriteDelayValue(&cur.delay_p->da[cur.k++], cur.time_type, max_v);
}

// §38.10 (Table 38-2): the both-flags arm - nine entries, min:typ:max of delay,
// then reject, then error.
void VpiWriteDelayRunBoth(DelayCursor& cur, const VpiDelayInfo& d) {
  VpiWriteMtmTriple(cur, d.min_delay, d.typ_delay, d.max_delay);
  VpiWriteMtmTriple(cur, d.min_reject, d.typ_reject, d.max_reject);
  VpiWriteMtmTriple(cur, d.min_error, d.typ_error, d.max_error);
}

// §38.10 (Table 38-2): emit one delay's run of da entries, selected by
// mtm_flag and pulsere_flag, starting at da[k] and advancing k past the run.
// The branch arms mirror Table 38-2 exactly: neither flag is one plain delay;
// mtm only is min/typ/max; pulsere only is delay/reject/error; both is the
// nine-entry min:typ:max of delay, reject, then error.
void VpiWriteDelayRun(DelayCursor& cur, bool mtm, bool pulsere,
                      const VpiDelayInfo& d) {
  if (!mtm && !pulsere) {
    // Neither flag set: one entry, the plain delay.
    VpiWriteDelayValue(&cur.delay_p->da[cur.k++], cur.time_type, d.delay);
  } else if (mtm && !pulsere) {
    // min:typ:max only: three entries, min then typ then max delay.
    VpiWriteMtmTriple(cur, d.min_delay, d.typ_delay, d.max_delay);
  } else if (!mtm && pulsere) {
    // Pulse limits only: delay, reject limit, error limit.
    VpiWriteDelayValue(&cur.delay_p->da[cur.k++], cur.time_type, d.delay);
    VpiWriteDelayValue(&cur.delay_p->da[cur.k++], cur.time_type, d.reject);
    VpiWriteDelayValue(&cur.delay_p->da[cur.k++], cur.time_type, d.error);
  } else {
    // Both flags: nine entries - min:typ:max of delay, then reject, then
    // error.
    VpiWriteDelayRunBoth(cur, d);
  }
}

// §38.32 (Table 38-4): read a min:typ:max triple from da[cur.k..cur.k+2] into
// the three referenced stored-delay fields, advancing the cursor past the run.
void VpiReadMtmTriple(DelayCursor& cur, double& min_v, double& typ_v,
                      double& max_v) {
  min_v = VpiReadDelayValue(cur.delay_p->da[cur.k++], cur.time_type);
  typ_v = VpiReadDelayValue(cur.delay_p->da[cur.k++], cur.time_type);
  max_v = VpiReadDelayValue(cur.delay_p->da[cur.k++], cur.time_type);
}

// §38.32 (Table 38-4): the both-flags arm - nine entries, min:typ:max of delay,
// then reject, then error.
void VpiReadDelayRunBoth(DelayCursor& cur, VpiDelayInfo& d) {
  VpiReadMtmTriple(cur, d.min_delay, d.typ_delay, d.max_delay);
  VpiReadMtmTriple(cur, d.min_reject, d.typ_reject, d.max_reject);
  VpiReadMtmTriple(cur, d.min_error, d.typ_error, d.max_error);
}

// §38.32 (Table 38-4, the inverse of VpiWriteDelayRun): read one delay's run
// of da entries into the stored delay, selected by mtm_flag and pulsere_flag,
// starting at da[k] and advancing k past the run. Only the fields the flags
// select are written; every other field of the stored delay is left untouched,
// so when pulsere_flag is clear the reject/error limits keep their values.
void VpiReadDelayRun(DelayCursor& cur, bool mtm, bool pulsere,
                     VpiDelayInfo& d) {
  if (!mtm && !pulsere) {
    // Neither flag set: one entry, the plain delay.
    d.delay = VpiReadDelayValue(cur.delay_p->da[cur.k++], cur.time_type);
  } else if (mtm && !pulsere) {
    // min:typ:max only: three entries, min then typ then max delay.
    VpiReadMtmTriple(cur, d.min_delay, d.typ_delay, d.max_delay);
  } else if (!mtm && pulsere) {
    // Pulse limits only: delay, reject limit, error limit.
    d.delay = VpiReadDelayValue(cur.delay_p->da[cur.k++], cur.time_type);
    d.reject = VpiReadDelayValue(cur.delay_p->da[cur.k++], cur.time_type);
    d.error = VpiReadDelayValue(cur.delay_p->da[cur.k++], cur.time_type);
  } else {
    // Both flags: nine entries - min:typ:max of delay, then reject, then
    // error.
    VpiReadDelayRunBoth(cur, d);
  }
}

}  // namespace

void VpiContext::GetDelays(VpiHandle obj, VpiDelay* delay_p) {
  // §38.10 / §38.1: the structure and its da array are application-allocated.
  // With nothing to fill, or no object to read delays from, there is nothing
  // to do; the routine never allocates anything itself.
  if (delay_p == nullptr || obj == nullptr) return;

  // §37.14 detail 2: the delay routines are not applicable to an interface
  // port. Treat such a request as an error (§38.2) and leave the caller's array
  // alone.
  if (obj->type == vpiPort && !VpiPortDelaysApplicable(obj->port_type)) {
    last_error_.state = kVpiPLI;
    last_error_.level = kVpiError;
    last_error_.message =
        "vpi_get_delays(): delays are not applicable to an interface port";
    return;
  }

  // §38.10: the legal values for the number of delays are fixed by the object's
  // category. A request that is not legal for this object is an error; record
  // it (§38.2) and leave the caller's array untouched.
  if (!VpiNoOfDelaysLegal(obj->type, delay_p->no_of_delays,
                          obj->delays.size())) {
    last_error_.state = kVpiPLI;
    last_error_.level = kVpiError;
    last_error_.message =
        "vpi_get_delays(): the requested number of delays is not legal for "
        "this object";
    return;
  }

  if (delay_p->da == nullptr) return;

  const bool kMtm = delay_p->mtm_flag != 0;
  const bool kPulsere = delay_p->pulsere_flag != 0;
  const int kTt = delay_p->time_type;

  // §38.10 (Table 38-2): each delay occupies a run of da entries selected by
  // mtm_flag and pulsere_flag, and the delays appear in source order. Walk the
  // delays in order, emitting each delay's run before moving to the next.
  DelayCursor cur{delay_p, 0, kTt};
  for (int i = 0; i < delay_p->no_of_delays; ++i) {
    const VpiDelayInfo kD = (static_cast<size_t>(i) < obj->delays.size())
                                ? obj->delays[i]
                                : VpiDelayInfo{};
    VpiWriteDelayRun(cur, kMtm, kPulsere, kD);
  }
}

void VpiContext::PutDelays(VpiHandle obj, VpiDelay* delay_p) {
  // §38.32 / §38.1: the structure and its da array are application-allocated.
  // With no source values or no target object there is nothing to set; the
  // routine never allocates the caller's memory itself.
  if (delay_p == nullptr || obj == nullptr) return;

  // §37.14 detail 2: the delay routines do not apply to an interface port.
  // Treat such a request as an error (§38.2) and change nothing.
  if (obj->type == vpiPort && !VpiPortDelaysApplicable(obj->port_type)) {
    last_error_.state = kVpiPLI;
    last_error_.level = kVpiError;
    last_error_.message =
        "vpi_put_delays(): delays are not applicable to an interface port";
    return;
  }

  // §38.32: the legal number of delays is fixed by the object's category, the
  // same classification vpi_get_delays() uses. A request that is not legal for
  // this object is an error; record it (§38.2) and set nothing.
  if (!VpiNoOfDelaysLegal(obj->type, delay_p->no_of_delays,
                          obj->delays.size())) {
    last_error_.state = kVpiPLI;
    last_error_.level = kVpiError;
    last_error_.message =
        "vpi_put_delays(): the requested number of delays is not legal for "
        "this object";
    return;
  }

  if (delay_p->da == nullptr) return;

  const bool kMtm = delay_p->mtm_flag != 0;
  const bool kPulsere = delay_p->pulsere_flag != 0;
  const int kTt = delay_p->time_type;

  // Ensure there is a stored slot for every delay being set, preserving any
  // values already present so the pulse limits survive a delay-only write
  // (§38.32: pulse limits retain their prior values when only the delay is
  // altered).
  if (obj->delays.size() < static_cast<size_t>(delay_p->no_of_delays))
    obj->delays.resize(delay_p->no_of_delays);

  // §38.32 (Table 38-4, == the vpi_get_delays() Table 38-2 layout): each delay
  // occupies a run of da entries selected by mtm_flag and pulsere_flag, and the
  // delays are taken in source order. Only the fields the flags select are
  // written; every other field of the stored delay is left untouched, so when
  // pulsere_flag is clear the reject/error limits keep the values they had.
  DelayCursor cur{delay_p, 0, kTt};
  for (int i = 0; i < delay_p->no_of_delays; ++i) {
    VpiDelayInfo& d = obj->delays[i];
    VpiReadDelayRun(cur, kMtm, kPulsere, d);
  }
}

void VpiContext::SeedSaveData(int id, const char* data, int len) {
  // §38.9 / §38.32: append bytes to the save/restart store for `id`. This
  // stands in for the production writer vpi_put_data(); it does not touch the
  // read cursor, so a subsequent first vpi_get_data() reads from offset zero.
  if (data == nullptr || len <= 0) return;
  std::vector<char>& bytes = save_data_[id];
  bytes.insert(bytes.end(), data, data + len);
}

int VpiContext::GetData(int id, char* data_loc, int num_of_bytes) {
  // §38.9: legal only from an application routine running for reason
  // cbStartOfRestart or cbEndOfRestart. Any other context is a failure, which
  // the routine reports by returning 0.
  if (current_callback_reason_ != kCbStartOfRestart &&
      current_callback_reason_ != kCbEndOfRestart) {
    last_error_.state = kVpiPLI;
    last_error_.level = kVpiError;
    last_error_.message =
        "vpi_get_data() may only be called from a cbStartOfRestart or "
        "cbEndOfRestart application routine";
    return 0;
  }

  // §38.9: a null buffer, a non-positive request, or an id that was never saved
  // is a failure - return 0.
  auto it = save_data_.find(id);
  if (data_loc == nullptr || num_of_bytes <= 0 || it == save_data_.end()) {
    last_error_.state = kVpiPLI;
    last_error_.level = kVpiError;
    last_error_.message = "vpi_get_data() could not retrieve saved data";
    return 0;
  }

  const std::vector<char>& bytes = it->second;
  std::size_t& cursor = save_data_cursor_[id];
  const std::size_t kAvailable =
      (cursor < bytes.size()) ? bytes.size() - cursor : 0;

  if (static_cast<std::size_t>(num_of_bytes) > kAvailable) {
    // §38.9: asking for more than remains is a warning. Hand back the bytes
    // that are left, zero-fill the rest of the buffer, advance the cursor past
    // what was delivered, and return the count actually retrieved.
    const int kRetrieved = static_cast<int>(kAvailable);
    for (int i = 0; i < kRetrieved; ++i) data_loc[i] = bytes[cursor + i];
    for (int i = kRetrieved; i < num_of_bytes; ++i) data_loc[i] = '\0';
    cursor += kAvailable;
    last_error_.state = kVpiPLI;
    last_error_.level = kVpiWarning;
    last_error_.message =
        "vpi_get_data() requested more data than were saved for this id";
    return kRetrieved;
  }

  // §38.9: the normal case (and the explicitly-acceptable case of asking for
  // fewer bytes than were saved). Copy the request and advance the cursor so a
  // later call resumes where this one stopped.
  for (int i = 0; i < num_of_bytes; ++i) data_loc[i] = bytes[cursor + i];
  cursor += static_cast<std::size_t>(num_of_bytes);
  return num_of_bytes;
}

int VpiContext::PutData(int id, const char* data_loc, int num_of_bytes) {
  // §38.31: legal only from an application routine running for reason
  // cbStartOfSave or cbEndOfSave. Any other context is an error, which the
  // routine reports by returning zero bytes written.
  if (current_callback_reason_ != kCbStartOfSave &&
      current_callback_reason_ != kCbEndOfSave) {
    last_error_.state = kVpiPLI;
    last_error_.level = kVpiError;
    last_error_.message =
        "vpi_put_data() may only be called from a cbStartOfSave or "
        "cbEndOfSave application routine";
    return 0;
  }

  // §38.31: numOfBytes shall be greater than zero, and the source storage must
  // be supplied by the application. Either condition is a detected error, which
  // returns zero bytes written.
  if (data_loc == nullptr || num_of_bytes <= 0) {
    last_error_.state = kVpiPLI;
    last_error_.level = kVpiError;
    last_error_.message =
        "vpi_put_data() requires a non-null source and a positive byte count";
    return 0;
  }

  // §38.31: append the bytes to the save/restart store for this id. There is no
  // limit on how many times an id is written and no ordering constraint across
  // ids; storing the bytes contiguously lets vpi_get_data() (§38.9) read them
  // back later in chunks of any size. The return value is the number of bytes
  // written.
  std::vector<char>& bytes = save_data_[id];
  bytes.insert(bytes.end(), data_loc, data_loc + num_of_bytes);
  return num_of_bytes;
}

int VpiContext::PutUserData(VpiHandle obj, void* userdata) {
  // §38.33: the handle names the storage location of a user-defined system task
  // or system function call instance. A null handle, or a handle to any other
  // kind of object, has no such storage to write: that is a detected error
  // (§38.2) and the routine returns 0 with no association made.
  if (obj == nullptr ||
      (obj->type != vpiSysTaskCall && obj->type != vpiSysFuncCall)) {
    last_error_.state = kVpiPLI;
    last_error_.level = kVpiError;
    last_error_.message =
        "vpi_put_userdata() requires a system task or system function call "
        "handle";
    return 0;
  }

  // §38.33: associate the user-data value with the call instance so that a
  // later vpi_get_userdata() reads it back. Returns 1 on success.
  obj->user_data = userdata;
  return 1;
}

void* VpiContext::GetUserData(VpiHandle obj) {
  // §38.14: only a user-defined system task or system function call instance
  // has a user-data storage location to read. A null handle, or a handle to any
  // other kind of object, has none: that is a detected error (§38.2) and the
  // routine returns null.
  if (obj == nullptr ||
      (obj->type != vpiSysTaskCall && obj->type != vpiSysFuncCall)) {
    last_error_.state = kVpiPLI;
    last_error_.level = kVpiError;
    last_error_.message =
        "vpi_get_userdata() requires a system task or system function call "
        "handle";
    return nullptr;
  }

  // §38.14: return whatever vpi_put_userdata() (§38.33) last associated with
  // the call instance. When nothing was ever associated the field is null,
  // which is exactly the NULL the routine must return for "no user data". A
  // restart or a reset clears the field (§38.33), so a read here returns null
  // afterwards until the application sets it again.
  return obj->user_data;
}

void VpiContext::ClearUserDataForRestartOrReset() {
  // §38.33: a restart or a reset drops every call instance's user-data
  // association, so that afterwards vpi_get_userdata() returns null until the
  // application re-establishes it (typically from a cbEndOfRestart or
  // cbEndOfReset routine after restoring it with vpi_get_data()).
  for (VpiObject* candidate : all_objects_) {
    candidate->user_data = nullptr;
  }
}

// §38.21: split a possibly hierarchical name into its dot-separated path
// components, outermost scope first. A simple name yields a single component.
std::vector<std::string_view> VpiNamePathComponents(std::string_view name) {
  std::vector<std::string_view> parts;
  size_t start = 0;
  for (;;) {
    size_t dot = name.find('.', start);
    if (dot == std::string_view::npos) {
      parts.push_back(name.substr(start));
      break;
    }
    parts.push_back(name.substr(start, dot - start));
    start = dot + 1;
  }
  return parts;
}

}  // namespace delta
