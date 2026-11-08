#include <algorithm>
#include <cmath>
#include <cstddef>
#include <cstdint>
#include <cstdio>
#include <functional>
#include <string>
#include <string_view>
#include <unordered_set>
#include <vector>

#include "common/arena.h"
#include "common/lexical_limits.h"
#include "common/types.h"
#include "parser/ast_expr.h"
#include "simulator/net.h"
#include "simulator/scheduler.h"
#include "simulator/sdf_parser.h"
#include "simulator/sim_context.h"
#include "simulator/specify.h"
#include "simulator/specify_sdf.h"
#include "simulator/variable.h"
#include "simulator/vpi_constants.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_data_structs.h"
#include "simulator/vpi_delay_devices.h"
#include "simulator/vpi_internal.h"
#include "simulator/vpi_model_helpers1.h"
#include "simulator/vpi_model_helpers3.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_put_run_delays.h"
#include "simulator/vpi_user.h"

namespace delta {

VpiHandle VpiContext::RegisterSystf(s_vpi_systf_data* data) {
  if (!data) return nullptr;

  if (data->type != kVpiSysTask && data->type != kVpiSysFunc) {
    last_error_.state = kVpiPLI;
    last_error_.level = kVpiError;
    last_error_.message = VpiText(
        "system task or function registration must carry a type of vpiSysTask "
        "or vpiSysFunc");
    return nullptr;
  }

  if (data->type == kVpiSysFunc && data->sysfunctype != vpiIntFunc &&
      data->sysfunctype != vpiRealFunc && data->sysfunctype != vpiTimeFunc &&
      data->sysfunctype != vpiSizedFunc &&
      data->sysfunctype != vpiSizedSignedFunc) {
    last_error_.state = kVpiPLI;
    last_error_.level = kVpiError;
    last_error_.message = VpiText(
        "system function registration must carry a sysfunctype of vpiIntFunc, "
        "vpiRealFunc, vpiTimeFunc, vpiSizedFunc or vpiSizedSignedFunc");
    return nullptr;
  }

  if (!VpiSystfNameIsValid(data->tfname)) {
    last_error_.state = kVpiPLI;
    last_error_.level = kVpiError;
    last_error_.message = VpiText(
        "system task or function name must be '$' followed by one or more "
        "identifier characters");
    return nullptr;
  }

  if (std::string_view(data->tfname).size() > kMaxIdentifierLength) {
    last_error_.state = kVpiPLI;
    last_error_.level = kVpiError;
    last_error_.message = VpiText(
        "system task or function name exceeds the maximum identifier length");
    return nullptr;
  }

  if (elaboration_started_) {
    last_error_.state = kVpiPLI;
    last_error_.level = kVpiError;
    last_error_.message = VpiText(
        "system task or function registration must precede elaboration");
    return nullptr;
  }

  systfs_.push_back(*data);

  auto* systf_obj = AllocObject();
  systf_obj->type = kVpiCallback;
  systf_obj->index = static_cast<int>(systfs_.size() - 1);
  systf_obj->is_systf = true;
  systf_objects_.push_back(systf_obj);
  return systf_obj;
}

const s_vpi_systf_data* VpiContext::ResolveSystf(const char* name) const {
  if (name == nullptr) return nullptr;

  for (auto it = systfs_.rbegin(); it != systfs_.rend(); ++it) {
    if (std::string_view(it->tfname) == name) {
      return &*it;
    }
  }
  return nullptr;
}

bool VpiContext::CallRegisteredSystf(const char* name, const Expr* call_site,
                                     SimContext& ctx, Logic4Vec& result,
                                     Arena& arena) {
  const s_vpi_systf_data* data = ResolveSystf(name);
  if (data == nullptr) return false;

  VpiHandle call = MakeSystfCallObject(*data, call_site, ctx, arena, true);

  VpiHandle outer_call = CurrentSystfCall();
  SetCurrentSystfCall(call);
  if (data->calltf != nullptr) {
    EnterApplicationRoutine();
    data->calltf(data->user_data);
    LeaveApplicationRoutine();
  }
  SetCurrentSystfCall(outer_call);

  result = call->var->value;
  result.is_signed =
      data->type == kVpiSysFunc && (data->sysfunctype == vpiSizedSignedFunc ||
                                    data->sysfunctype == vpiIntFunc);
  return true;
}

void VpiContext::CallCompiletfForSourceCall(const s_vpi_systf_data& data,
                                            const Expr* call_site,
                                            SimContext& ctx, Arena& arena) {
  if (data.compiletf == nullptr) return;

  VpiHandle call = MakeSystfCallObject(data, call_site, ctx, arena, false);

  VpiHandle outer_call = CurrentSystfCall();
  SetCurrentSystfCall(call);
  EnterApplicationRoutine();
  VpiSystfInvoke(data.compiletf, data.user_data);
  LeaveApplicationRoutine();
  SetCurrentSystfCall(outer_call);
}

void VpiContext::GetSystfInfo(VpiHandle obj, s_vpi_systf_data* systf_data_p) {
  if (obj == nullptr || systf_data_p == nullptr) return;

  if (obj->type != kVpiCallback || !obj->is_systf) return;

  *systf_data_p = systfs_[static_cast<std::size_t>(obj->index)];
}

void VpiContext::GetCbInfo(VpiHandle obj, s_cb_data* cb_data_p) {
  if (obj == nullptr || cb_data_p == nullptr) return;

  if (obj->type != kVpiCallback || obj->is_systf) return;
  if (obj->index < 0) return;

  *cb_data_p = callbacks_[static_cast<std::size_t>(obj->index)];
}

VpiHandle VpiContext::CreateTimeQueue() {
  auto* obj = AllocObject();
  obj->type = kVpiTimeQueue;
  return obj;
}

void VpiContext::GetTime(VpiHandle obj, s_vpi_time* time_p) {
  if (time_p == nullptr) return;

  uint64_t ticks = 0;
  bool use_sim_time_unit = (obj == nullptr);
  if (obj != nullptr && obj->type == kVpiTimeQueue) {
    ticks = obj->has_scheduled_time
                ? obj->time_queue_time
                : (scheduler_ ? scheduler_->NextEventTime().ticks : 0);
    use_sim_time_unit = true;
  } else {
    ticks = scheduler_ ? scheduler_->CurrentTime().ticks : 0;
  }

  if (time_p->type == kVpiScaledRealTime) {
    int target_unit = use_sim_time_unit
                          ? sim_time_unit_
                          : VpiObjectTimeUnit(*obj, sim_time_unit_);
    double scale =
        std::pow(10.0, static_cast<double>(sim_time_unit_ - target_unit));
    time_p->real = static_cast<double>(ticks) * scale;
  } else {
    time_p->high = static_cast<uint32_t>(ticks >> 32);
    time_p->low = static_cast<uint32_t>(ticks & 0xFFFFFFFFu);
  }
}

bool VpiIsPrimitiveType(int type) {
  switch (type) {
    case vpiGate:
    case vpiSwitch:
    case vpiUdp:
      return true;
    default:
      return false;
  }
}

bool VpiObjectIsPrimitive(int type) {
  return VpiIsPrimitiveType(type) || type == vpiPrimitive;
}

namespace {

struct DelayCursor {
  s_vpi_delay* delay_p;
  int k;
  int time_type;
  double ticks_per_unit;
};

bool VpiNoOfDelaysLegal(int type, int n, size_t available) {
  if (VpiObjectIsPrimitive(type)) return n == 2 || n == 3;
  if (type == vpiModPath)
    return n == 1 || n == 2 || n == 3 || n == 6 || n == 12;
  if (type == vpiInterModPath) return n == 2 || n == 3;
  if (type == vpiPort || type == vpiPortBit) return n == 2 || n == 3;
  if (type == vpiContAssign) return n == 2 || n == 3;
  if (type == vpiTchk) return available > 0 && n == static_cast<int>(available);
  if (type == vpiDelayControl) return n == 1;
  return false;
}

void VpiWriteDelayValue(s_vpi_time* slot, const DelayCursor& cur,
                        double value) {
  slot->type = cur.time_type;
  slot->high = 0;
  slot->low = 0;
  slot->real = 0.0;
  if (cur.time_type == vpiScaledRealTime) {
    slot->real = value / cur.ticks_per_unit;
  } else if (cur.time_type == vpiSimTime) {
    auto ticks = static_cast<uint64_t>(value);
    slot->high = static_cast<uint32_t>(ticks >> 32);
    slot->low = static_cast<uint32_t>(ticks & 0xFFFFFFFFu);
  }
}

double VpiReadDelayValue(const s_vpi_time& slot, const DelayCursor& cur) {
  if (cur.time_type == vpiScaledRealTime) {
    return slot.real * cur.ticks_per_unit;
  }
  if (cur.time_type == vpiSimTime) {
    uint64_t ticks = (static_cast<uint64_t>(slot.high) << 32) | slot.low;
    return static_cast<double>(ticks);
  }
  return 0.0;
}

void VpiWriteMtmTriple(DelayCursor& cur, double min_v, double typ_v,
                       double max_v) {
  VpiWriteDelayValue(&cur.delay_p->da[cur.k++], cur, min_v);
  VpiWriteDelayValue(&cur.delay_p->da[cur.k++], cur, typ_v);
  VpiWriteDelayValue(&cur.delay_p->da[cur.k++], cur, max_v);
}

void VpiWriteDelayRunBoth(DelayCursor& cur, const VpiDelayInfo& d) {
  VpiWriteMtmTriple(cur, d.min_delay, d.typ_delay, d.max_delay);
  VpiWriteMtmTriple(cur, d.min_reject, d.typ_reject, d.max_reject);
  VpiWriteMtmTriple(cur, d.min_error, d.typ_error, d.max_error);
}

void VpiWriteDelayRun(DelayCursor& cur, bool mtm, bool pulsere,
                      const VpiDelayInfo& d) {
  if (!mtm && !pulsere) {
    VpiWriteDelayValue(&cur.delay_p->da[cur.k++], cur, d.delay);
  } else if (mtm && !pulsere) {
    VpiWriteMtmTriple(cur, d.min_delay, d.typ_delay, d.max_delay);
  } else if (!mtm) {
    VpiWriteDelayValue(&cur.delay_p->da[cur.k++], cur, d.delay);
    VpiWriteDelayValue(&cur.delay_p->da[cur.k++], cur, d.reject);
    VpiWriteDelayValue(&cur.delay_p->da[cur.k++], cur, d.error);
  } else {
    VpiWriteDelayRunBoth(cur, d);
  }
}

void VpiReadMtmTriple(DelayCursor& cur, double& min_v, double& typ_v,
                      double& max_v) {
  min_v = VpiReadDelayValue(cur.delay_p->da[cur.k++], cur);
  typ_v = VpiReadDelayValue(cur.delay_p->da[cur.k++], cur);
  max_v = VpiReadDelayValue(cur.delay_p->da[cur.k++], cur);
}

void VpiReadDelayRunBoth(DelayCursor& cur, VpiDelayInfo& d) {
  VpiReadMtmTriple(cur, d.min_delay, d.typ_delay, d.max_delay);
  VpiReadMtmTriple(cur, d.min_reject, d.typ_reject, d.max_reject);
  VpiReadMtmTriple(cur, d.min_error, d.typ_error, d.max_error);
}

void VpiReadDelayRun(DelayCursor& cur, bool mtm, bool pulsere,
                     VpiDelayInfo& d) {
  if (!mtm && !pulsere) {
    d.delay = VpiReadDelayValue(cur.delay_p->da[cur.k++], cur);
  } else if (mtm && !pulsere) {
    VpiReadMtmTriple(cur, d.min_delay, d.typ_delay, d.max_delay);
  } else if (!mtm) {
    d.delay = VpiReadDelayValue(cur.delay_p->da[cur.k++], cur);
    d.reject = VpiReadDelayValue(cur.delay_p->da[cur.k++], cur);
    d.error = VpiReadDelayValue(cur.delay_p->da[cur.k++], cur);
  } else {
    VpiReadDelayRunBoth(cur, d);
  }
}

}  // namespace

static std::vector<VpiDelayInfo> DelayControlDelays(
    VpiHandle control, int sim_unit,
    const std::function<double(VpiHandle)>& value_of) {
  VpiHandle expr = VpiDelayControlDelayExpr(control);
  if (expr == nullptr) return {};
  const double kScale =
      std::pow(10.0, VpiObjectTimeUnit(*control, sim_unit) - sim_unit);
  VpiDelayInfo info;
  info.delay = value_of(expr) * kScale;
  info.min_delay = info.delay;
  info.typ_delay = info.delay;
  info.max_delay = info.delay;
  if (expr->type == vpiOperation && expr->op_type == vpiMinTypMaxOp &&
      expr->children.size() == 3) {
    info.min_delay = value_of(expr->children[0]) * kScale;
    info.typ_delay = value_of(expr->children[1]) * kScale;
    info.max_delay = value_of(expr->children[2]) * kScale;
  }
  return {info};
}

void VpiContext::GetDelays(VpiHandle obj, s_vpi_delay* delay_p) {
  if (delay_p == nullptr || obj == nullptr) return;

  if (obj->type == vpiPort && !VpiPortDelaysApplicable(obj->port_type)) {
    last_error_.state = kVpiPLI;
    last_error_.level = kVpiError;
    last_error_.message = VpiText(
        "vpi_get_delays(): delays are not applicable to an interface port");
    return;
  }

  const std::vector<VpiDelayInfo> kDelays =
      obj->type != vpiDelayControl
          ? obj->delays
          : DelayControlDelays(obj, sim_time_unit_, [this](VpiHandle expr) {
              s_vpi_value value = {};
              value.format = vpiRealVal;
              GetValue(expr, &value);
              return value.value.real;
            });
  if (!VpiNoOfDelaysLegal(obj->type, delay_p->no_of_delays, kDelays.size())) {
    last_error_.state = kVpiPLI;
    last_error_.level = kVpiError;
    last_error_.message = VpiText(
        "vpi_get_delays(): the requested number of delays is not legal for "
        "this object");
    return;
  }

  if (delay_p->da == nullptr) return;

  const bool kMtm = delay_p->mtm_flag != 0;
  const bool kPulsere = delay_p->pulsere_flag != 0;
  const int kTt = delay_p->time_type;

  DelayCursor cur{
      delay_p, 0, kTt,
      std::pow(10.0, VpiObjectTimeUnit(*obj, sim_time_unit_) - sim_time_unit_)};
  for (int i = 0; i < delay_p->no_of_delays; ++i) {
    const VpiDelayInfo kD =
        (static_cast<size_t>(i) < kDelays.size()) ? kDelays[i] : VpiDelayInfo{};
    VpiWriteDelayRun(cur, kMtm, kPulsere, kD);
  }
}

static void AnnotateContAssignDelays(const VpiObject& obj, SimContext& sim) {
  const std::size_t kDot = obj.run_key.rfind('.');
  const std::string kPrefix =
      kDot == std::string::npos ? "" : obj.run_key.substr(0, kDot + 1);
  const std::string_view kNet =
      std::string_view(obj.run_key)
          .substr(kDot == std::string::npos ? 0 : kDot + 1);
  uint64_t delays[3] = {};
  for (std::size_t i = 0; i < 3 && i < obj.delays.size(); ++i) {
    delays[i] = static_cast<uint64_t>(std::llround(obj.delays[i].delay));
  }
  if (obj.delays.size() == 2) delays[2] = std::min(delays[0], delays[1]);
  sim.AcquireSpecifyManager().AnnotateDriverDelays(kPrefix, kNet, delays);
}

static std::string InterconnectPortName(const VpiObject& port) {
  const std::string& instance = port.parent->full_name;
  return instance.substr(instance.find('.') + 1) + "." + std::string(port.name);
}

static void AnnotateInterconnectDelays(const VpiObject& obj, SimContext& sim) {
  SdfInterconnectAnnotation annotation;
  if (obj.type == vpiInterModPath) {
    annotation.source = InterconnectPortName(*obj.children[0]);
    annotation.load = InterconnectPortName(*obj.children[1]);
  } else {
    annotation.construct = SdfInterconnectConstruct::kPort;
    annotation.load = InterconnectPortName(obj);
  }
  std::vector<SdfDelayValue> values;
  for (const VpiDelayInfo& delay : obj.delays) {
    SdfDelayValue& value = values.emplace_back();
    value.typ_val = static_cast<uint64_t>(std::llround(delay.delay));
  }
  const std::vector<uint64_t> kExpanded =
      ExpandSdfDelays(values, SdfMtm::kTypical);
  for (std::size_t i = 0; i < kExpanded.size(); ++i) {
    annotation.delays[i] = kExpanded[i];
  }
  sim.AcquireSpecifyManager().AnnotateSdfInterconnect(annotation);
}

void VpiContext::PutDelays(VpiHandle obj, s_vpi_delay* delay_p) {
  if (delay_p == nullptr || obj == nullptr) return;

  if (obj->type == vpiPort && !VpiPortDelaysApplicable(obj->port_type)) {
    last_error_.state = kVpiPLI;
    last_error_.level = kVpiError;
    last_error_.message = VpiText(
        "vpi_put_delays(): delays are not applicable to an interface port");
    return;
  }

  if (!VpiNoOfDelaysLegal(obj->type, delay_p->no_of_delays,
                          obj->delays.size())) {
    last_error_.state = kVpiPLI;
    last_error_.level = kVpiError;
    last_error_.message = VpiText(
        "vpi_put_delays(): the requested number of delays is not legal for "
        "this object");
    return;
  }

  if (delay_p->da == nullptr) return;

  const bool kMtm = delay_p->mtm_flag != 0;
  const bool kPulsere = delay_p->pulsere_flag != 0;
  const int kTt = delay_p->time_type;

  if (obj->delays.size() < static_cast<size_t>(delay_p->no_of_delays))
    obj->delays.resize(delay_p->no_of_delays);

  DelayCursor cur{
      delay_p, 0, kTt,
      std::pow(10.0, VpiObjectTimeUnit(*obj, sim_time_unit_) - sim_time_unit_)};
  for (int i = 0; i < delay_p->no_of_delays; ++i) {
    VpiDelayInfo& d = obj->delays[i];
    VpiReadDelayRun(cur, kMtm, kPulsere, d);
  }
  if (obj->type == vpiContAssign && !obj->run_key.empty()) {
    AnnotateContAssignDelays(*obj, *sim_ctx_);
  }
  const auto kAlloc = [this] { return AllocObject(); };
  if (obj->type == vpiInterModPath &&
      VpiPlaceInterModPathDevice(obj, kAlloc) != nullptr) {
    AnnotateInterconnectDelays(*obj, *sim_ctx_);
  }
  if (obj->type == vpiPort && VpiPlacePortDelayDevice(obj, kAlloc) != nullptr) {
    AnnotateInterconnectDelays(*obj, *sim_ctx_);
  }
  if (sim_ctx_ != nullptr) VpiPutRunDelays(*obj, run_entry_index_, *sim_ctx_);
}

void VpiContext::SeedSaveData(int id, const char* data, int len) {
  if (data == nullptr || len <= 0) return;
  std::vector<char>& bytes = save_data_[id];
  bytes.insert(bytes.end(), data, data + len);
}

int VpiContext::GetData(int id, char* data_loc, int num_of_bytes) {
  if (current_callback_reason_ != kCbStartOfRestart &&
      current_callback_reason_ != kCbEndOfRestart) {
    last_error_.state = kVpiPLI;
    last_error_.level = kVpiError;
    last_error_.message = VpiText(
        "vpi_get_data() may only be called from a cbStartOfRestart or "
        "cbEndOfRestart application routine");
    return 0;
  }

  auto it = save_data_.find(id);
  if (data_loc == nullptr || num_of_bytes <= 0 || it == save_data_.end()) {
    last_error_.state = kVpiPLI;
    last_error_.level = kVpiError;
    last_error_.message =
        VpiText("vpi_get_data() could not retrieve saved data");
    return 0;
  }

  const std::vector<char>& bytes = it->second;
  std::size_t& cursor = save_data_cursor_[id];
  const std::size_t kAvailable =
      (cursor < bytes.size()) ? bytes.size() - cursor : 0;

  if (static_cast<std::size_t>(num_of_bytes) > kAvailable) {
    const int kRetrieved = static_cast<int>(kAvailable);
    for (int i = 0; i < kRetrieved; ++i) data_loc[i] = bytes[cursor + i];
    for (int i = kRetrieved; i < num_of_bytes; ++i) data_loc[i] = '\0';
    cursor += kAvailable;
    last_error_.state = kVpiPLI;
    last_error_.level = kVpiWarning;
    last_error_.message = VpiText(
        "vpi_get_data() requested more data than were saved for this id");
    return kRetrieved;
  }

  for (int i = 0; i < num_of_bytes; ++i) data_loc[i] = bytes[cursor + i];
  cursor += static_cast<std::size_t>(num_of_bytes);
  return num_of_bytes;
}

int VpiContext::PutData(int id, const char* data_loc, int num_of_bytes) {
  if (current_callback_reason_ != kCbStartOfSave &&
      current_callback_reason_ != kCbEndOfSave) {
    last_error_.state = kVpiPLI;
    last_error_.level = kVpiError;
    last_error_.message = VpiText(
        "vpi_put_data() may only be called from a cbStartOfSave or "
        "cbEndOfSave application routine");
    return 0;
  }

  if (data_loc == nullptr || num_of_bytes <= 0) {
    last_error_.state = kVpiPLI;
    last_error_.level = kVpiError;
    last_error_.message = VpiText(
        "vpi_put_data() requires a non-null source and a positive byte count");
    return 0;
  }

  std::vector<char>& bytes = save_data_[id];
  bytes.insert(bytes.end(), data_loc, data_loc + num_of_bytes);
  return num_of_bytes;
}

static bool VpiIsUserDefinedCall(VpiHandle obj) {
  return obj != nullptr &&
         (obj->type == vpiSysTaskCall || obj->type == vpiSysFuncCall) &&
         obj->user_defined;
}

int VpiContext::PutUserData(VpiHandle obj, void* userdata) {
  if (!VpiIsUserDefinedCall(obj)) {
    last_error_.state = kVpiPLI;
    last_error_.level = kVpiError;
    last_error_.message = VpiText(
        "vpi_put_userdata() requires a user-defined system task or system "
        "function call handle");
    return 0;
  }

  obj->user_data = userdata;
  return 1;
}

void* VpiContext::GetUserData(VpiHandle obj) {
  if (!VpiIsUserDefinedCall(obj)) {
    last_error_.state = kVpiPLI;
    last_error_.level = kVpiError;
    last_error_.message = VpiText(
        "vpi_get_userdata() requires a user-defined system task or system "
        "function call handle");
    return nullptr;
  }

  return obj->user_data;
}

void VpiContext::ClearUserDataForRestartOrReset() {
  for (VpiObject* candidate : all_objects_) {
    candidate->user_data = nullptr;
  }
}

std::vector<std::string_view> VpiNamePathComponents(
    std::string_view name,
    const std::unordered_set<std::string_view>& whole_names) {
  std::vector<std::string_view> parts;
  std::size_t start = 0;
  for (;;) {
    std::size_t end = std::min(name.find('.', start), name.size());
    for (std::size_t cut = end; cut < name.size();) {
      cut = std::min(name.find('.', cut + 1), name.size());
      if (whole_names.contains(name.substr(start, cut - start))) end = cut;
    }
    parts.push_back(name.substr(start, end - start));
    if (end == name.size()) break;
    start = end + 1;
  }
  return parts;
}

namespace {

constexpr std::string_view kWhiteSpace = " \t\n\r\f\v";

std::size_t SeparatorLength(std::string_view name, std::size_t i) {
  if (i >= name.size()) return 0;
  if (name[i] == '.') return 1;
  return name.substr(i, 2) == "::" ? 2 : 0;
}

std::size_t ComponentEnd(std::string_view name, std::size_t i) {
  if (name[i] == '\\') {
    return std::min(name.find_first_of(kWhiteSpace, i), name.size());
  }
  std::size_t end = i;
  while (end < name.size() && SeparatorLength(name, end) == 0) ++end;
  return end;
}

}  // namespace

std::vector<std::string_view> VpiHandleNameComponents(std::string_view name) {
  std::vector<std::string_view> parts;
  std::size_t i = 0;
  while (i < name.size()) {
    const std::size_t kEnd = ComponentEnd(name, i);
    const bool kEscaped = name[i] == '\\';
    parts.push_back(kEscaped ? name.substr(i + 1, kEnd - i - 1)
                             : name.substr(i, kEnd - i));
    std::size_t next = kEnd;
    if (kEscaped) {
      next = std::min(name.find_first_not_of(kWhiteSpace, kEnd), name.size());
    }
    const std::size_t kSeparator = SeparatorLength(name, next);
    if (kSeparator == 0) break;
    i = next + kSeparator;
  }
  return parts;
}

}  // namespace delta
