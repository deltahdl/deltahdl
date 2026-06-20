#include "simulator/vpi.h"

#include <algorithm>
#include <cctype>
#include <cmath>
#include <cstdarg>
#include <cstddef>
#include <cstdint>
#include <cstdio>
#include <string>
#include <string_view>
#include <vector>

#include "common/types.h"
#include "simulator/dpi.h"
#include "simulator/net.h"
#include "simulator/scheduler.h"
#include "simulator/sim_context.h"
// §37.10 detail 3: the package/interface/program instance kinds are defined in
// the SystemVerilog VPI header alongside the §37.10 vpiInstance relation.
#include "simulator/sv_vpi_user.h"
#include "simulator/variable.h"

#include "simulator/vpi_internal.h"

namespace delta {

void VpiContext::Attach(SimContext& sim_ctx) {
  for (auto& [name, var] : sim_ctx.GetVariables()) {
    auto* obj = AllocObject();
    obj->type = kVpiReg;
    obj->name = name;
    obj->var = var;
    obj->size = static_cast<int>(var->value.width);
    object_map_[name] = obj;
  }
}

VpiHandle VpiContext::RegisterSystf(VpiSystfData* data) {
  if (!data) return nullptr;

  // §36.9.1: a user-defined system task or system function name shall begin
  // with a dollar sign. §38.37.1 sharpens this: the dollar sign shall be
  // followed by one or more characters that are legal in a SystemVerilog simple
  // identifier. Refuse a name that fails either part of the rule (a missing or
  // bare "$", or any illegal trailing character).
  if (!VpiSystfNameIsValid(data->tfname)) {
    last_error_.state = kVpiError;
    last_error_.level = kVpiError;
    last_error_.message =
        "system task or function name must be '$' followed by one or more "
        "identifier characters";
    return nullptr;
  }

  // §36.9.1: the registration of system tasks shall occur prior to elaboration
  // or the resolution of references. Once elaboration has begun the window has
  // closed, so reject the registration.
  if (elaboration_started_) {
    last_error_.state = kVpiError;
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
    ticks = scheduler_ ? scheduler_->NextEventTime().ticks : 0;
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

// §38.10: the four object categories that carry delays. Their legal
// no_of_delays values differ, so vpi_get_delays() classifies the object first.
bool VpiObjectIsPrimitive(int type) {
  return type == vpiGate || type == vpiSwitch || type == vpiUdp ||
         type == vpiPrimitive || type == vpiSeqPrim || type == vpiCombPrim;
}

namespace {

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
    last_error_.state = kVpiError;
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
    last_error_.state = kVpiError;
    last_error_.level = kVpiError;
    last_error_.message =
        "vpi_get_delays(): the requested number of delays is not legal for "
        "this object";
    return;
  }

  if (delay_p->da == nullptr) return;

  const bool mtm = delay_p->mtm_flag != 0;
  const bool pulsere = delay_p->pulsere_flag != 0;
  const int tt = delay_p->time_type;

  // §38.10 (Table 38-2): each delay occupies a run of da entries selected by
  // mtm_flag and pulsere_flag, and the delays appear in source order. Walk the
  // delays in order, emitting each delay's run before moving to the next.
  int k = 0;
  for (int i = 0; i < delay_p->no_of_delays; ++i) {
    const VpiDelayInfo d = (static_cast<size_t>(i) < obj->delays.size())
                               ? obj->delays[i]
                               : VpiDelayInfo{};
    if (!mtm && !pulsere) {
      // Neither flag set: one entry, the plain delay.
      VpiWriteDelayValue(&delay_p->da[k++], tt, d.delay);
    } else if (mtm && !pulsere) {
      // min:typ:max only: three entries, min then typ then max delay.
      VpiWriteDelayValue(&delay_p->da[k++], tt, d.min_delay);
      VpiWriteDelayValue(&delay_p->da[k++], tt, d.typ_delay);
      VpiWriteDelayValue(&delay_p->da[k++], tt, d.max_delay);
    } else if (!mtm && pulsere) {
      // Pulse limits only: delay, reject limit, error limit.
      VpiWriteDelayValue(&delay_p->da[k++], tt, d.delay);
      VpiWriteDelayValue(&delay_p->da[k++], tt, d.reject);
      VpiWriteDelayValue(&delay_p->da[k++], tt, d.error);
    } else {
      // Both flags: nine entries - min:typ:max of delay, then reject, then
      // error.
      VpiWriteDelayValue(&delay_p->da[k++], tt, d.min_delay);
      VpiWriteDelayValue(&delay_p->da[k++], tt, d.typ_delay);
      VpiWriteDelayValue(&delay_p->da[k++], tt, d.max_delay);
      VpiWriteDelayValue(&delay_p->da[k++], tt, d.min_reject);
      VpiWriteDelayValue(&delay_p->da[k++], tt, d.typ_reject);
      VpiWriteDelayValue(&delay_p->da[k++], tt, d.max_reject);
      VpiWriteDelayValue(&delay_p->da[k++], tt, d.min_error);
      VpiWriteDelayValue(&delay_p->da[k++], tt, d.typ_error);
      VpiWriteDelayValue(&delay_p->da[k++], tt, d.max_error);
    }
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
    last_error_.state = kVpiError;
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
    last_error_.state = kVpiError;
    last_error_.level = kVpiError;
    last_error_.message =
        "vpi_put_delays(): the requested number of delays is not legal for "
        "this object";
    return;
  }

  if (delay_p->da == nullptr) return;

  const bool mtm = delay_p->mtm_flag != 0;
  const bool pulsere = delay_p->pulsere_flag != 0;
  const int tt = delay_p->time_type;

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
  int k = 0;
  for (int i = 0; i < delay_p->no_of_delays; ++i) {
    VpiDelayInfo& d = obj->delays[i];
    if (!mtm && !pulsere) {
      // Neither flag set: one entry, the plain delay.
      d.delay = VpiReadDelayValue(delay_p->da[k++], tt);
    } else if (mtm && !pulsere) {
      // min:typ:max only: three entries, min then typ then max delay.
      d.min_delay = VpiReadDelayValue(delay_p->da[k++], tt);
      d.typ_delay = VpiReadDelayValue(delay_p->da[k++], tt);
      d.max_delay = VpiReadDelayValue(delay_p->da[k++], tt);
    } else if (!mtm && pulsere) {
      // Pulse limits only: delay, reject limit, error limit.
      d.delay = VpiReadDelayValue(delay_p->da[k++], tt);
      d.reject = VpiReadDelayValue(delay_p->da[k++], tt);
      d.error = VpiReadDelayValue(delay_p->da[k++], tt);
    } else {
      // Both flags: nine entries - min:typ:max of delay, then reject, then
      // error.
      d.min_delay = VpiReadDelayValue(delay_p->da[k++], tt);
      d.typ_delay = VpiReadDelayValue(delay_p->da[k++], tt);
      d.max_delay = VpiReadDelayValue(delay_p->da[k++], tt);
      d.min_reject = VpiReadDelayValue(delay_p->da[k++], tt);
      d.typ_reject = VpiReadDelayValue(delay_p->da[k++], tt);
      d.max_reject = VpiReadDelayValue(delay_p->da[k++], tt);
      d.min_error = VpiReadDelayValue(delay_p->da[k++], tt);
      d.typ_error = VpiReadDelayValue(delay_p->da[k++], tt);
      d.max_error = VpiReadDelayValue(delay_p->da[k++], tt);
    }
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
    last_error_.state = kVpiError;
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
    last_error_.state = kVpiError;
    last_error_.level = kVpiError;
    last_error_.message = "vpi_get_data() could not retrieve saved data";
    return 0;
  }

  const std::vector<char>& bytes = it->second;
  std::size_t& cursor = save_data_cursor_[id];
  const std::size_t available =
      (cursor < bytes.size()) ? bytes.size() - cursor : 0;

  if (static_cast<std::size_t>(num_of_bytes) > available) {
    // §38.9: asking for more than remains is a warning. Hand back the bytes
    // that are left, zero-fill the rest of the buffer, advance the cursor past
    // what was delivered, and return the count actually retrieved.
    const int retrieved = static_cast<int>(available);
    for (int i = 0; i < retrieved; ++i) data_loc[i] = bytes[cursor + i];
    for (int i = retrieved; i < num_of_bytes; ++i) data_loc[i] = '\0';
    cursor += available;
    last_error_.state = kVpiWarning;
    last_error_.level = kVpiWarning;
    last_error_.message =
        "vpi_get_data() requested more data than were saved for this id";
    return retrieved;
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
    last_error_.state = kVpiError;
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
    last_error_.state = kVpiError;
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
    last_error_.state = kVpiError;
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
    last_error_.state = kVpiError;
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
