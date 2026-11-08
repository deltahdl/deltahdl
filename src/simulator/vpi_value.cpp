#include <algorithm>
#include <cmath>
#include <cstddef>
#include <cstdint>
#include <cstdio>
#include <deque>
#include <functional>
#include <optional>
#include <utility>
#include <vector>

#include "common/arena.h"
#include "common/packed_range.h"
#include "common/types.h"
#include "simulator/class_object.h"
#include "simulator/evaluation.h"
#include "simulator/net.h"
#include "simulator/scheduler.h"
#include "simulator/sim_context.h"
#include "simulator/statement_assign.h"
#include "simulator/stmt_exec.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/variable.h"
#include "simulator/vpi_collection_elements.h"
#include "simulator/vpi_constants.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_delay_devices.h"
#include "simulator/vpi_expr_values.h"
#include "simulator/vpi_internal.h"
#include "simulator/vpi_model_helpers1.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_primitive_value.h"
#include "simulator/vpi_table_entry_value.h"
#include "simulator/vpi_user.h"
#include "simulator/vpi_value_numbers.h"
#include "simulator/vpi_value_pools.h"
#include "simulator/vpi_value_refusals.h"
#include "simulator/vpi_value_strings.h"

namespace delta {

static int ScalarFromBits(uint64_t aval, uint64_t bval) {
  if (!bval) return aval ? kVpi1 : kVpi0;
  return aval ? kVpiX : kVpiZ;
}

static void GetValueVector(const Logic4Vec& v, s_vpi_value* value,
                           std::vector<std::vector<s_vpi_vecval>>& pool) {
  int width = static_cast<int>(v.width);
  const int kGroups = (width + 31) / 32;
  std::vector<s_vpi_vecval> vec(static_cast<size_t>(std::max(kGroups, 1)));
  for (int i = 0; i < kGroups; ++i) {
    const Logic4Word& word = v.words[i / 2];
    int shift = (i % 2) * 32;
    auto a32 = static_cast<uint32_t>((word.aval >> shift) & 0xFFFFFFFFu);
    auto b32 = static_cast<uint32_t>((word.bval >> shift) & 0xFFFFFFFFu);
    vec[static_cast<size_t>(i)].aval = a32;
    vec[static_cast<size_t>(i)].bval = b32;
  }
  pool.push_back(std::move(vec));
  value->value.vector = pool.back().data();
}

static void GetValueStrength(
    const Logic4Vec& v, s_vpi_value* value,
    std::vector<std::vector<s_vpi_strengthval>>& pool) {
  int width = static_cast<int>(v.width);
  std::vector<s_vpi_strengthval> arr(
      static_cast<size_t>(std::max(width, 1)),
      s_vpi_strengthval{kVpi0, vpiStrongDrive, vpiStrongDrive});
  for (int i = 0; i < width; ++i) {
    const Logic4Word& word = v.words[i / 64];
    const int kBit = i % 64;
    arr[static_cast<size_t>(i)].logic =
        ScalarFromBits((word.aval >> kBit) & 1, (word.bval >> kBit) & 1);
  }
  pool.push_back(std::move(arr));
  value->value.strength = pool.back().data();
}

static void GetValueIntVal(const Logic4Vec& v, s_vpi_value* value) {
  value->value.integer = static_cast<int>(VpiKnownIntegerValue(v));
}

static void GetValueTime(const Logic4Vec& v, s_vpi_value* value,
                         std::deque<s_vpi_time>& pool) {
  const uint64_t kValue = v.ToUint64();
  s_vpi_time& time = pool.emplace_back();
  time.type = vpiSimTime;
  time.high = static_cast<PLI_UINT32>(kValue >> 32);
  time.low = static_cast<PLI_UINT32>(kValue & 0xFFFFFFFFu);
  time.real = 0.0;
  value->value.time = &time;
}

static double ObjectRealValue(const Logic4Vec& v) { return RealVecToDouble(v); }

static void GetValueObjType(const Logic4Vec& v, s_vpi_value* value,
                            std::vector<std::vector<s_vpi_vecval>>& pool) {
  if (v.is_real) {
    value->format = kVpiRealVal;
    value->value.real = ObjectRealValue(v);
  } else if (v.width == 1) {
    value->format = kVpiScalarVal;
    value->value.scalar =
        ScalarFromBits(v.words[0].aval & 1, v.words[0].bval & 1);
  } else {
    value->format = kVpiVectorVal;
    GetValueVector(v, value, pool);
  }
}

static void RecordVpiError(s_vpi_error_info& error, const char* message) {
  error.state = kVpiPLI;
  error.level = kVpiError;
  error.message = VpiText(message);
}

static void DispatchIntegerFormat(const Logic4Vec& v, s_vpi_value* value,
                                  VpiValuePools& pools) {
  switch (value->format) {
    case kVpiIntVal:
      GetValueIntVal(v, value);
      break;
    case kVpiRealVal:
      value->value.real = v.is_signed
                              ? static_cast<double>(VpiKnownIntegerValue(v))
                              : static_cast<double>(v.ToUint64());
      break;
    case kVpiScalarVal:
      value->value.scalar =
          ScalarFromBits(v.words[0].aval & 1, v.words[0].bval & 1);
      break;
    case kVpiBinStrVal:
      GetValueBinStr(v, value, pools.strings);
      break;
    case kVpiDecStrVal:
      GetValueDecStr(v, value, pools.strings);
      break;
    case kVpiHexStrVal:
      GetValueHexStr(v, value, pools.strings);
      break;
    case kVpiOctStrVal:
      GetValueOctStr(v, value, pools.strings);
      break;
    case kVpiStringVal:
      GetValueStringVal(v, value, pools.strings);
      break;
    case kVpiTimeVal:
      GetValueTime(v, value, pools.times);
      break;
    case kVpiVectorVal:
      GetValueVector(v, value, pools.vectors);
      break;
    case kVpiStrengthVal:
      GetValueStrength(v, value, pools.strengths);
      break;
    case kVpiObjTypeVal:
      GetValueObjType(v, value, pools.vectors);
      break;
    default:
      break;
  }
}

static Logic4Word BitOfValue(const Logic4Vec& whole, int offset) {
  const auto kWord = static_cast<uint32_t>(offset) / 64;
  const uint32_t kShift = static_cast<uint32_t>(offset) % 64;
  return Logic4Word{(whole.words[kWord].aval >> kShift) & 1,
                    (whole.words[kWord].bval >> kShift) & 1};
}

static Logic4Vec SliceOfValue(const Logic4Vec& whole, int64_t offset, int width,
                              std::vector<Logic4Word>& words) {
  words.assign((static_cast<std::size_t>(width) + 63) / 64, Logic4Word{0, 0});
  for (int k = 0; k < width; ++k) {
    const Logic4Word kBit = BitOfValue(whole, static_cast<int>(offset + k));
    words[k / 64].aval |= kBit.aval << (k % 64);
    words[k / 64].bval |= kBit.bval << (k % 64);
  }
  Logic4Vec view;
  view.width = static_cast<uint32_t>(width);
  view.nwords = static_cast<uint32_t>(words.size());
  view.words = words.data();
  return view;
}

static void DispatchValueByFormat(const Logic4Vec& v, s_vpi_value* value,
                                  VpiValuePools& pools);

static void DispatchGetValueByFormat(VpiHandle obj, s_vpi_value* value,
                                     VpiValuePools& pools) {
  if (obj->bit_offset >= 0) {
    std::vector<Logic4Word> words;
    const Logic4Vec kSlice = SliceOfValue(obj->var->value, obj->bit_offset,
                                          std::max(obj->size, 1), words);
    DispatchIntegerFormat(kSlice, value, pools);
    return;
  }
  Logic4Vec whole = obj->var->value;
  const bool kDeclared = obj->decl_signed || obj->var->is_signed;
  whole.is_signed = obj->var->declared_type != nullptr
                        ? kDeclared
                        : whole.is_signed || kDeclared;
  DispatchValueByFormat(whole, value, pools);
}

static void DispatchValueByFormat(const Logic4Vec& v, s_vpi_value* value,
                                  VpiValuePools& pools) {
  if (v.is_real) {
    if (value->format == kVpiObjTypeVal) {
      GetValueObjType(v, value, pools.vectors);
      return;
    }
    double d = ObjectRealValue(v);
    if (value->format == kVpiRealVal) {
      value->value.real = d;
      return;
    }
    if (value->format == kVpiStringVal) {
      char buf[64];
      std::snprintf(buf, sizeof(buf), "%.16g", d);
      pools.strings.emplace_back(buf);
      value->value.str = VpiText(pools.strings.back().c_str());
      return;
    }
    auto rounded = static_cast<uint64_t>(std::llround(d));
    Logic4Word iw{rounded, 0};
    Logic4Vec int_view;
    int_view.width = 64;
    int_view.nwords = 1;
    int_view.words = &iw;
    DispatchIntegerFormat(int_view, value, pools);
    return;
  }
  DispatchIntegerFormat(v, value, pools);
}

static const PackedRange* VaryingSelectDim(const VpiObject& obj) {
  return obj.select_dim.has_value() ? &*obj.select_dim : nullptr;
}

static std::optional<int64_t> VaryingIndex(const VpiObject& obj,
                                           SimContext* sim) {
  if (obj.index_expr == nullptr) return std::nullopt;
  VpiObject& index = *obj.index_expr;
  Logic4Vec held;
  if (index.var != nullptr) {
    VpiRefreshElementCopy(index);
    held = index.var->value;
  } else {
    held = VpiEvaluateExpressionObject(index, *sim);
  }
  if (!held.IsKnown()) return std::nullopt;
  return SelectBoundValue(held);
}

static std::optional<int64_t> VaryingOffset(const VpiObject& obj,
                                            const PackedRange& dim,
                                            SimContext* sim) {
  const std::optional<int64_t> kIndex = VaryingIndex(obj, sim);
  if (!kIndex || !dim.Contains(*kIndex)) return std::nullopt;
  return obj.select_base_offset +
         (dim.OffsetOf(*kIndex) * std::max(obj.size, 1));
}

static void DispatchUnselected(int width, bool is_4state, s_vpi_value* value,
                               VpiValuePools& pools) {
  const uint64_t kFill = is_4state ? ~uint64_t{0} : 0;
  std::vector<Logic4Word> words((static_cast<std::size_t>(width) + 63) / 64,
                                Logic4Word{kFill, kFill});
  if (width % 64 != 0) {
    const uint64_t kMask = (uint64_t{1} << (width % 64)) - 1;
    words.back().aval &= kMask;
    words.back().bval &= kMask;
  }
  Logic4Vec fill;
  fill.width = static_cast<uint32_t>(width);
  fill.nwords = static_cast<uint32_t>(words.size());
  fill.words = words.data();
  DispatchIntegerFormat(fill, value, pools);
}

static void GetVaryingSelectValue(VpiHandle obj, const PackedRange& dim,
                                  s_vpi_value* value, VpiValuePools& pools,
                                  SimContext* sim) {
  const Variable& whole = *obj->var;
  const int kWidth = std::max(obj->size, 1);
  if (const std::optional<int64_t> kOffset = VaryingOffset(*obj, dim, sim)) {
    std::vector<Logic4Word> words;
    DispatchIntegerFormat(SliceOfValue(whole.value, *kOffset, kWidth, words),
                          value, pools);
    return;
  }
  DispatchUnselected(kWidth, whole.is_4state, value, pools);
}

VpiObject* VpiVarSelectElement(const VpiObject& select, SimContext* sim) {
  const VpiObject* from = select.parent->type == vpiVarSelect
                              ? VpiVarSelectElement(*select.parent, sim)
                              : select.parent;
  const std::optional<int64_t> kIndex = VaryingIndex(select, sim);
  if (from == nullptr || !kIndex) return nullptr;
  for (VpiObject* child : from->children) {
    if (child->array_member && child->index == *kIndex) return child;
  }
  return nullptr;
}

static const VpiObject& AnyElement(const VpiObject& select) {
  const VpiObject* member = select.parent;
  while (member->type == vpiVarSelect) member = member->parent;
  while (member->type == vpiArrayVar) {
    member = *std::ranges::find_if(
        member->children,
        [](const VpiObject* child) { return child->array_member; });
  }
  return *member;
}

static void BindRunStorage(VpiObject& obj, SimContext* sim) {
  if (obj.var == nullptr && !obj.run_key.empty()) {
    obj.var = sim->FindVariable(obj.run_key);
  }
}

static VpiHandle ValueStandIn(VpiHandle obj, s_vpi_value* value,
                              VpiValuePools& pools, SimContext* sim) {
  if (VpiHandle source = VpiPrimitiveValueSource(obj); source != obj) {
    return source;
  }
  if (obj->type == vpiDelayTerm) {
    const Net* run_net = obj->term_net->net;
    if (obj->parent->in_term == obj && run_net != nullptr &&
        run_net->pending_path_value) {
      DispatchValueByFormat(*run_net->pending_path_value, value, pools);
      return nullptr;
    }
    return VpiDelayTermValueNet(*obj);
  }
  if (obj->type == vpiVarSelect) {
    if (VpiHandle element = VpiVarSelectElement(*obj, sim)) return element;
    const VpiObject& element = AnyElement(*obj);
    DispatchUnselected(element.size, element.var->is_4state, value, pools);
    return nullptr;
  }
  return obj;
}

static void GetStoragelessValue(const VpiObject& obj, s_vpi_value* value,
                                VpiValuePools& pools, SimContext* sim) {
  if (obj.expr_scope == nullptr) return;
  if (obj.type == vpiContAssignBit) {
    std::vector<Logic4Word> words;
    DispatchIntegerFormat(SliceOfValue(VpiEvaluateExpressionObject(obj, *sim),
                                       obj.bit_offset, 1, words),
                          value, pools);
    return;
  }
  DispatchValueByFormat(VpiEvaluateExpressionObject(obj, *sim), value, pools);
}

static void GetTableEntryVector(const VpiObject& obj, s_vpi_value* value,
                                VpiValuePools& pools) {
  s_vpi_value row = {};
  row.format = kVpiStringVal;
  GetValueStringVal(obj.var->value, &row, pools.strings);
  pools.vectors.push_back(VpiTableEntryVector(row.value.str));
  value->value.vector = pools.vectors.back().data();
}

void VpiContext::GetValue(VpiHandle obj, s_vpi_value* value) {
  if (!obj || !value) return;
  if (VpiReadSealed(*obj)) {
    last_error_.state = kVpiPLI;
    last_error_.level = kVpiError;
    last_error_.message =
        VpiText("vpi_get_value() on a protected object is an error");
    return;
  }
  if (VpiExpressionHasSideEffects(obj)) {
    ++obj->side_effect_count;
  }
  if (VpiGetValueIsRefused(obj, *value, last_error_)) return;
  if (VpiHandle stand_in = ValueStandIn(obj, value, value_pools_, sim_ctx_);
      stand_in != obj) {
    if (stand_in != nullptr) GetValue(stand_in, value);
    return;
  }
  VpiRefreshElementCopy(*obj);
  BindRunStorage(*obj, sim_ctx_);
  if (!obj->var) {
    GetStoragelessValue(*obj, value, value_pools_, sim_ctx_);
    return;
  }
  if (const PackedRange* dim = VaryingSelectDim(*obj)) {
    GetVaryingSelectValue(obj, *dim, value, value_pools_, sim_ctx_);
    return;
  }
  if (obj->type == vpiTableEntry && value->format == kVpiVectorVal) {
    GetTableEntryVector(*obj, value, value_pools_);
    return;
  }
  if (value->format == kVpiObjTypeVal)
    value->format = VpiObjTypeFormat(obj->type);
  DispatchGetValueByFormat(obj, value, value_pools_);
}

static bool PutValueFormatIsRejected(VpiHandle obj, const s_vpi_value* value,
                                     s_vpi_error_info& error) {
  if (value->format == kVpiStringVal && obj->var->value.is_real) {
    RecordVpiError(error,
                   "vpi_put_value(): vpiStringVal is not a legal format for a "
                   "real object");
    return true;
  }

  if (value->format == kVpiStrengthVal && obj->var->value.width > 1) {
    RecordVpiError(
        error,
        "vpi_put_value(): vpiStrengthVal is not a legal format for a "
        "vector object");
    return true;
  }
  return false;
}

static std::optional<double> RealPutValue(const s_vpi_value& value) {
  if (value.format == kVpiRealVal) return value.value.real;
  std::vector<Logic4Word> words;
  if (!VpiPutValueBits(value, 64, words)) return std::nullopt;
  return static_cast<double>(
      static_cast<int64_t>(words.front().aval & ~words.front().bval));
}

static void PutValueWriteBits(VpiHandle obj, const s_vpi_value* value) {
  const uint32_t kWidth = VpiPutWidth(*obj);
  std::vector<Logic4Word> bits;
  if (obj->var->is_real || obj->var->value.is_real) {
    const std::optional<double> kReal = RealPutValue(*value);
    if (!kReal) return;
    Arena scratch;
    const Logic4Vec kBits = MakeRealVec(scratch, *kReal, kWidth);
    bits.assign(kBits.words, kBits.words + kBits.nwords);
    VpiWriteDecodedBits(*obj, bits, kWidth);
    obj->var->value.is_real = true;
    return;
  }
  if (VpiPutValueBits(*value, kWidth, bits)) {
    VpiWriteDecodedBits(*obj, bits, kWidth);
  }
}

static bool PutValueResolveWritableTarget(VpiHandle obj, Scheduler* scheduler,
                                          SimContext* sim) {
  if (!obj->var && !obj->net) return true;

  if (!obj->var) {
    if (scheduler) scheduler->NoteWriteAttempt();
    return true;
  }

  if (obj->var->is_event) {
    if (scheduler != nullptr && sim != nullptr) {
      TriggerEvent(obj->var, *sim);
    } else if (scheduler) {
      obj->var->triggered_ticks = scheduler->CurrentTime().ticks;
    }
    return true;
  }
  return false;
}

static void PutValueApplyWriteAndForce(VpiHandle obj, const s_vpi_value* value,
                                       int mode, Scheduler* scheduler) {
  if (scheduler) scheduler->NoteWriteAttempt();

  PutValueWriteBits(obj, value);
  obj->var->NotifyWatchers();

  if (mode == vpiForceFlag) {
    obj->var->is_forced = true;
    obj->var->force_active = true;
    obj->var->held_parts.assign(1, Variable::HeldPart{});
    obj->var->forced_value = obj->var->value;
  }
}

static bool PutValueHasDelay(int mode, const s_vpi_time* time) {
  bool immediate =
      (mode == vpiNoDelay || mode == vpiForceFlag || mode == vpiReleaseFlag);
  return !immediate && time &&
         (time->low != 0 || time->high != 0 || time->real != 0.0);
}

static bool PutValueDelayModeIsRejected(VpiHandle obj, int mode, bool has_delay,
                                        s_vpi_error_info& error) {
  if (obj->prim_type == vpiSeqPrim &&
      (mode == vpiInertialDelay || mode == vpiTransportDelay ||
       mode == vpiPureTransportDelay)) {
    RecordVpiError(error,
                   "vpi_put_value(): a sequential UDP must be written with the "
                   "vpiNoDelay flag");
    return true;
  }

  if (obj->automatic && has_delay) {
    RecordVpiError(error,
                   "vpi_put_value(): a value with a delay may not be put on an "
                   "automatic variable");
    return true;
  }
  return false;
}

static bool PutValueIsSealed(const VpiObject& obj, s_vpi_error_info& error) {
  if (!VpiWriteSealed(obj)) return false;
  RecordVpiError(error, "vpi_put_value() on a protected object is an error");
  return true;
}

static VpiHandle PutValueTargetOf(VpiHandle obj,
                                  const std::function<VpiObject*()>& alloc,
                                  SimContext* sim) {
  if (obj->type == vpiVarSelect) return VpiVarSelectElement(*obj, sim);
  const PackedRange* dim = VaryingSelectDim(*obj);
  if (dim == nullptr) return obj;
  const std::optional<int64_t> kOffset = VaryingOffset(*obj, *dim, sim);
  if (!kOffset) return nullptr;
  VpiObject* slice = alloc();
  slice->type = obj->type;
  slice->parent = obj->parent;
  slice->var = obj->parent->var;
  slice->net = obj->parent->net;
  slice->size = obj->size;
  slice->bit_offset = static_cast<int>(*kOffset);
  return slice;
}

static void NotifyPropertyWrite(const VpiObject& obj, SimContext& ctx) {
  const ClassObject& owner = *obj.property_of;
  const ClassTypeInfo* declarer = owner.type->StaticPropertyDeclarer(obj.name);
  if (declarer != nullptr) {
    declarer->NotifyStaticWatchers();
    return;
  }
  ctx.NotifyClassHandleWatchers(owner.handle);
}

static VpiHandle CancelScheduledEvent(VpiHandle obj) {
  if (obj->type != vpiSchedEvent) return nullptr;
  if (obj->scheduled && obj->put_superseded) *obj->put_superseded = true;
  obj->scheduled = false;
  return nullptr;
}

static bool PutValueRefusedInReadOnlySynch(bool at_read_only_synch, int flags,
                                           s_vpi_error_info& error) {
  if (!at_read_only_synch || (flags & ~vpiReturnEvent) == vpiCancelEvent) {
    return false;
  }
  RecordVpiError(error,
                 "vpi_put_value(): no value may be written from a "
                 "cbReadOnlySynch callback");
  return true;
}

static void PutValueRelease(VpiObject& obj, SimContext* sim) {
  if (sim != nullptr) {
    ReleaseForcedTarget(obj.var, obj.net, *sim, sim->GetArena());
  } else {
    obj.var->is_forced = false;
    obj.var->force_active = false;
    obj.var->held_parts.clear();
  }
}

struct PutValueRun {
  Scheduler* scheduler;
  SimContext* sim;
  int sim_time_unit;
  std::function<VpiObject*()> alloc;
};

static VpiHandle PutValueWrite(VpiObject* obj, s_vpi_value* value,
                               const s_vpi_time* time, int flags,
                               const PutValueRun& run) {
  const bool kReturnEvent = (flags & vpiReturnEvent) != 0;
  const int kMode = flags & ~vpiReturnEvent;
  const bool kHasDelay = PutValueHasDelay(kMode, time);
  if (kHasDelay && run.scheduler != nullptr) {
    VpiObject* event = run.alloc();
    event->event_time = run.scheduler->CurrentTime().ticks +
                        VpiPutDelayTicks(*obj, *time, run.sim_time_unit);
    VpiSchedulePut(*obj, *value, kMode, *run.scheduler, *event);
    return kReturnEvent ? event : nullptr;
  }

  PutValueApplyWriteAndForce(obj, value, kMode, run.scheduler);
  if (!kHasDelay) VpiStoreElementCopy(*obj);
  if (obj->property_of != nullptr) {
    NotifyPropertyWrite(*obj, *run.sim);
  }

  if (!kReturnEvent || !kHasDelay) return nullptr;
  VpiObject* ev = run.alloc();
  ev->type = vpiSchedEvent;
  ev->scheduled = true;
  return ev;
}

VpiHandle VpiContext::PutValue(VpiHandle obj, s_vpi_value* value,
                               s_vpi_time* time, int flags) {
  if (!obj) return nullptr;
  if (PutValueIsSealed(*obj, last_error_) ||
      VpiPutValueTargetIsRejected(obj, last_error_) ||
      PutValueRefusedInReadOnlySynch(at_read_only_synch_time_, flags,
                                     last_error_)) {
    return nullptr;
  }

  int mode = flags & ~vpiReturnEvent;

  if (mode == vpiCancelEvent) {
    CancelScheduledEvent(obj);
    if (obj->type == vpiSchedEvent) ReleaseHandle(obj);
    return nullptr;
  }

  obj = PutValueTargetOf(obj, [this] { return AllocObject(); }, sim_ctx_);
  if (obj == nullptr) return nullptr;

  bool has_delay = PutValueHasDelay(mode, time);

  if (PutValueDelayModeIsRejected(obj, mode, has_delay, last_error_) ||
      VpiPutSequentialUdpValue(*obj, value, sim_ctx_)) {
    return nullptr;
  }

  BindRunStorage(*obj, sim_ctx_);
  if (PutValueResolveWritableTarget(obj, scheduler_, sim_ctx_)) return nullptr;

  if (!value || PutValueFormatIsRejected(obj, value, last_error_)) {
    return nullptr;
  }

  if (mode == vpiReleaseFlag) {
    PutValueRelease(*obj, sim_ctx_);
    GetValue(obj, value);
    return nullptr;
  }

  return PutValueWrite(
      obj, value, time, flags,
      {scheduler_, sim_ctx_, sim_time_unit_, [this] { return AllocObject(); }});
}

}  // namespace delta
