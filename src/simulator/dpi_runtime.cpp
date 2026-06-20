#include "simulator/dpi_runtime.h"

#include <algorithm>
#include <cmath>
#include <cstdint>
#include <list>
#include <map>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "simulator/sv_vpi_user.h"

namespace delta {

// §35.9 disable-protocol state for the current execution thread. A foreign
// routine queries its disabled state with no handle, so the state is naturally
// thread-local, mirroring how the C-ABI scope (g_current_scope) is held. The
// acknowledgement flag records whether svAckDisabledState() was called during
// the current disable episode; it is cleared whenever the disabled state is
// left so each episode starts unacknowledged.
namespace {
thread_local bool g_disabled_state = false;
thread_local bool g_disable_acked = false;
}  // namespace

bool DpiCurrentDisabledState() { return g_disabled_state; }

void DpiSetCurrentDisabledState(bool disabled) {
  g_disabled_state = disabled;
  // The acknowledgement is per disable episode: leaving the disabled state ends
  // the episode, so a subsequent one starts unacknowledged.
  if (!disabled) g_disable_acked = false;
}

void DpiAckCurrentDisable() { g_disable_acked = true; }

bool DpiCurrentDisableAcknowledged() { return g_disable_acked; }

namespace {
// §H.9.3 scope-name registry storage. std::list keeps element addresses stable
// as scopes are added, so a handle handed to C code stays valid for the life of
// the simulation. The by-name index drives svGetScopeFromName().
std::list<DpiScope>& DpiScopeRegistryStorage() {
  static std::list<DpiScope> storage;
  return storage;
}
std::map<std::string, DpiScope*, std::less<>>& DpiScopeRegistryByName() {
  static std::map<std::string, DpiScope*, std::less<>> by_name;
  return by_name;
}
}  // namespace

const DpiScope* DpiRegisterScope(std::string_view name) {
  auto& by_name = DpiScopeRegistryByName();
  auto it = by_name.find(name);
  if (it != by_name.end()) return it->second;
  DpiScope& scope = DpiScopeRegistryStorage().emplace_back();
  scope.name = std::string(name);
  by_name.emplace(scope.name, &scope);
  return &scope;
}

const DpiScope* DpiScopeFromName(std::string_view name) {
  auto& by_name = DpiScopeRegistryByName();
  auto it = by_name.find(name);
  return it == by_name.end() ? nullptr : it->second;
}

const char* DpiNameFromScope(const DpiScope* scope) {
  if (scope == nullptr) return "";
  // Only handles this registry produced map back to a name; an unregistered
  // pointer is not a recognized scope, so it yields an empty name rather than a
  // dereference of an unknown address.
  for (const DpiScope& s : DpiScopeRegistryStorage()) {
    if (&s == scope) return s.name.c_str();
  }
  return "";
}

DpiArgValue DpiArgValue::FromInt(int32_t v) {
  DpiArgValue a;
  a.type = DataTypeKind::kInt;
  a.data.int_val = v;
  return a;
}

DpiArgValue DpiArgValue::FromLongint(int64_t v) {
  DpiArgValue a;
  a.type = DataTypeKind::kLongint;
  a.data.longint_val = v;
  return a;
}

DpiArgValue DpiArgValue::FromReal(double v) {
  DpiArgValue a;
  a.type = DataTypeKind::kReal;
  a.data.real_val = v;
  return a;
}

DpiArgValue DpiArgValue::FromString(std::string v) {
  DpiArgValue a;
  a.type = DataTypeKind::kString;
  a.string_val = std::move(v);
  return a;
}

DpiArgValue DpiArgValue::FromChandle(SvChandle v) {
  DpiArgValue a;
  a.type = DataTypeKind::kChandle;
  a.data.chandle_val = v;
  return a;
}

DpiArgValue DpiArgValue::FromBit(SvBit v) {
  DpiArgValue a;
  a.type = DataTypeKind::kBit;
  a.data.bit_val = v;
  return a;
}

DpiArgValue DpiArgValue::FromLogic(SvLogic v) {
  DpiArgValue a;
  a.type = DataTypeKind::kLogic;
  a.data.logic_val = v;
  return a;
}

int32_t DpiArgValue::AsInt() const { return data.int_val; }
int64_t DpiArgValue::AsLongint() const { return data.longint_val; }
double DpiArgValue::AsReal() const { return data.real_val; }
const std::string& DpiArgValue::AsString() const { return string_val; }
SvChandle DpiArgValue::AsChandle() const { return data.chandle_val; }
SvBit DpiArgValue::AsBit() const { return data.bit_val; }
SvLogic DpiArgValue::AsLogic() const { return data.logic_val; }

namespace {

// Read any numeric DPI argument value as an integer. Real values round to the
// nearest integer, matching the way SystemVerilog assignments convert a real
// expression to an integral target — §35.6.1 requires the temporary/actual
// assignments to follow general SystemVerilog assignment and coercion rules.
int64_t NumericToInt(const DpiArgValue& v) {
  switch (v.type) {
    case DataTypeKind::kReal:
    case DataTypeKind::kShortreal:
    case DataTypeKind::kRealtime:
      return static_cast<int64_t>(std::llround(v.AsReal()));
    case DataTypeKind::kLongint:
    case DataTypeKind::kTime:
      return v.AsLongint();
    case DataTypeKind::kBit:
      return v.AsBit();
    case DataTypeKind::kLogic:
    case DataTypeKind::kReg:
      return v.AsLogic();
    default:
      return v.AsInt();
  }
}

// Read any numeric DPI argument value as a real, used when coercing toward a
// floating-point formal or actual.
double NumericToReal(const DpiArgValue& v) {
  switch (v.type) {
    case DataTypeKind::kReal:
    case DataTypeKind::kShortreal:
    case DataTypeKind::kRealtime:
      return v.AsReal();
    case DataTypeKind::kLongint:
    case DataTypeKind::kTime:
      return static_cast<double>(v.AsLongint());
    case DataTypeKind::kBit:
      return static_cast<double>(v.AsBit());
    case DataTypeKind::kLogic:
    case DataTypeKind::kReg:
      return static_cast<double>(v.AsLogic());
    default:
      return static_cast<double>(v.AsInt());
  }
}

// §35.6.1: when a coercion is needed, the value crosses the interface through a
// temporary that is created with the appropriate coercion. This realizes that
// temporary: it returns `v` converted to `target`, following SystemVerilog
// assignment/coercion rules. When the value already has the target type no
// conversion is needed and it is returned unchanged.
DpiArgValue CoerceArgValue(const DpiArgValue& v, DataTypeKind target) {
  if (v.type == target) return v;
  switch (target) {
    case DataTypeKind::kReal:
    case DataTypeKind::kShortreal:
    case DataTypeKind::kRealtime: {
      DpiArgValue r = DpiArgValue::FromReal(NumericToReal(v));
      r.type = target;
      return r;
    }
    case DataTypeKind::kLongint:
    case DataTypeKind::kTime: {
      DpiArgValue r = DpiArgValue::FromLongint(NumericToInt(v));
      r.type = target;
      return r;
    }
    case DataTypeKind::kBit:
      return DpiArgValue::FromBit(static_cast<SvBit>(NumericToInt(v) & 1));
    case DataTypeKind::kLogic:
    case DataTypeKind::kReg: {
      DpiArgValue r =
          DpiArgValue::FromLogic(static_cast<SvLogic>(NumericToInt(v) & 1));
      r.type = target;
      return r;
    }
    case DataTypeKind::kByte: {
      DpiArgValue r =
          DpiArgValue::FromInt(static_cast<int8_t>(NumericToInt(v)));
      r.type = target;
      return r;
    }
    case DataTypeKind::kShortint: {
      DpiArgValue r =
          DpiArgValue::FromInt(static_cast<int16_t>(NumericToInt(v)));
      r.type = target;
      return r;
    }
    case DataTypeKind::kString:
      // No numeric/string coercion is defined across the interface here; a
      // string actual is carried through unchanged toward a string formal and
      // any other source yields the empty string.
      return v.type == DataTypeKind::kString ? v : DpiArgValue::FromString("");
    case DataTypeKind::kChandle:
      return v.type == DataTypeKind::kChandle
                 ? v
                 : DpiArgValue::FromChandle(nullptr);
    default: {  // kInt, kInteger, and any other integral formal
      DpiArgValue r =
          DpiArgValue::FromInt(static_cast<int32_t>(NumericToInt(v)));
      r.type = target;
      return r;
    }
  }
}

// §35.6.2: equality of two same-typed actual-argument values. After an
// imported function returns, the copy-back leaves an output/inout actual with
// its own declared type, so the value before the call and the value after it
// share a type; this compares them so a value-change event is propagated only
// when the call genuinely changed the actual, matching SystemVerilog
// value-change semantics where an assignment of an unchanged value is inert.
bool SameArgValue(const DpiArgValue& a, const DpiArgValue& b) {
  if (a.type != b.type) return false;
  switch (a.type) {
    case DataTypeKind::kReal:
    case DataTypeKind::kShortreal:
    case DataTypeKind::kRealtime:
      return a.AsReal() == b.AsReal();
    case DataTypeKind::kLongint:
    case DataTypeKind::kTime:
      return a.AsLongint() == b.AsLongint();
    case DataTypeKind::kString:
      return a.AsString() == b.AsString();
    case DataTypeKind::kChandle:
      return a.AsChandle() == b.AsChandle();
    case DataTypeKind::kBit:
      return a.AsBit() == b.AsBit();
    case DataTypeKind::kLogic:
    case DataTypeKind::kReg:
      return a.AsLogic() == b.AsLogic();
    default:
      return a.AsInt() == b.AsInt();
  }
}

}  // namespace

void DpiRuntime::RegisterImport(DpiRtFunction func) {
  import_index_[func.sv_name] = imports_.size();
  imports_.push_back(std::move(func));
}

const DpiRtFunction* DpiRuntime::FindImport(std::string_view sv_name) const {
  auto it = import_index_.find(sv_name);
  if (it == import_index_.end()) return nullptr;
  return &imports_[it->second];
}

bool DpiRuntime::HasImport(std::string_view sv_name) const {
  return import_index_.count(sv_name) != 0;
}

uint32_t DpiRuntime::ImportCount() const {
  return static_cast<uint32_t>(imports_.size());
}

void DpiRuntime::RegisterExport(DpiRtExport exp) {
  // §35.7: exported SystemVerilog functions are always context functions.
  // Normalize the flag here so any caller that fails to set it (or sets it
  // false) still gets a context export.
  exp.is_context = true;
  export_index_[exp.sv_name] = exports_.size();
  exports_.push_back(std::move(exp));
}

const DpiRtExport* DpiRuntime::FindExport(std::string_view sv_name) const {
  auto it = export_index_.find(sv_name);
  if (it == export_index_.end()) return nullptr;
  return &exports_[it->second];
}

bool DpiRuntime::HasExport(std::string_view sv_name) const {
  return export_index_.count(sv_name) != 0;
}

uint32_t DpiRuntime::ExportCount() const {
  return static_cast<uint32_t>(exports_.size());
}

DpiArgValue DpiRuntime::CallImport(std::string_view sv_name,
                                   const std::vector<DpiArgValue>& args) const {
  const auto* func = FindImport(sv_name);
  if (!func || !func->impl) return DpiArgValue::FromInt(0);
  return func->impl(args);
}

DpiArgValue DpiRuntime::UndeterminedOutputValue(DataTypeKind type) {
  // §35.5.1.2: the initial value of an output argument is undetermined and
  // implementation dependent. We pick a deterministic per-type zero so the
  // callee observes a value that is independent of the caller's actual.
  switch (type) {
    case DataTypeKind::kLongint:
    case DataTypeKind::kTime:
      return DpiArgValue::FromLongint(0);
    case DataTypeKind::kReal:
    case DataTypeKind::kShortreal:
    case DataTypeKind::kRealtime:
      return DpiArgValue::FromReal(0.0);
    case DataTypeKind::kString:
      return DpiArgValue::FromString("");
    case DataTypeKind::kChandle:
      return DpiArgValue::FromChandle(nullptr);
    case DataTypeKind::kBit:
      return DpiArgValue::FromBit(0);
    case DataTypeKind::kLogic:
    case DataTypeKind::kReg:
      return DpiArgValue::FromLogic(0);
    default:
      return DpiArgValue::FromInt(0);
  }
}

DpiArgValue DpiRuntime::CallImportWithArgs(
    std::string_view sv_name, std::vector<DpiArgValue>& actuals) const {
  const auto* func = FindImport(sv_name);
  if (!func) return DpiArgValue::FromInt(0);

  // The vector the foreign function operates on. Input and inout arguments are
  // seeded with the caller's actual value, so the foreign function can read an
  // inout argument's initial value. An output argument is seeded with an
  // undetermined value instead of the actual, because the foreign function
  // shall not assume anything about an output argument's initial value.
  std::vector<DpiArgValue> callee = actuals;
  for (size_t i = 0; i < func->args.size() && i < callee.size(); ++i) {
    if (func->args[i].direction == Direction::kOutput) {
      callee[i] = UndeterminedOutputValue(func->args[i].type);
    } else {
      // §35.6.1: input and inout formals are passed copy-in through a temporary
      // initialized with the actual coerced to the formal's type. When the
      // actual already matches the formal type CoerceArgValue is a no-op, so
      // the §35.5.1.2 same-type behavior is preserved.
      callee[i] = CoerceArgValue(callee[i], func->args[i].type);
    }
  }

  DpiArgValue result = DpiArgValue::FromInt(0);
  if (func->arg_impl) {
    result = func->arg_impl(callee);
  } else if (func->impl) {
    result = func->impl(callee);
  }

  // §35.9: when a disable is in effect, the values of an imported subroutine's
  // output and inout parameters are undefined, as is its return value. A
  // SystemVerilog simulator is not obligated to propagate anything the foreign
  // code wrote back to the calling SystemVerilog code. This implementation
  // exercises that latitude: the actuals are left untouched and an undetermined
  // result of the return type is yielded, so no disabled-call value leaks out.
  if (DpiCurrentDisabledState()) {
    return UndeterminedOutputValue(func->return_type);
  }

  // Copy back only output and inout arguments: the value the foreign function
  // wrote to them is visible outside the call. Input arguments are passed by
  // value, so any modification the foreign function made to its copy is
  // discarded here and the caller's actual is left unchanged.
  for (size_t i = 0; i < func->args.size() && i < actuals.size(); ++i) {
    Direction dir = func->args[i].direction;
    if (dir == Direction::kOutput || dir == Direction::kInout) {
      // §35.6.1: copy-out assigns the temporary's value back to the actual with
      // the appropriate conversion — coerce the foreign-written value to the
      // actual argument's own type. A matching type makes this a no-op.
      actuals[i] = CoerceArgValue(callee[i], actuals[i].type);
    }
  }
  return result;
}

DpiArgValue DpiRuntime::CallImportDetectingChanges(
    std::string_view sv_name, std::vector<DpiArgValue>& actuals,
    std::vector<DpiArgValueChange>& changes) const {
  const auto* func = FindImport(sv_name);
  if (!func) return DpiArgValue::FromInt(0);

  // §35.6.2: snapshot the actuals before the call so that, once control
  // returns, the simulator can tell which output/inout actuals the call
  // changed. Nothing is detected or propagated yet — that happens only after
  // the imported function has returned.
  std::vector<DpiArgValue> before = actuals;

  // The copy-back of output/inout values into the actuals is the
  // §35.5.1.2/§35.6.1 responsibility of CallImportWithArgs and finishes before
  // any value-change event below is raised.
  DpiArgValue result = CallImportWithArgs(sv_name, actuals);

  // §35.6.2: now that control has returned, handle the value changes. Propagate
  // each as if the actual were assigned the formal immediately after the
  // return. Only output and inout actuals can change. Walk the arguments in
  // declaration order so that, with more than one argument, the assignments and
  // their value-change events follow the order general SystemVerilog rules
  // impose. An actual whose value the call did not alter raises no event.
  for (size_t i = 0; i < func->args.size() && i < actuals.size(); ++i) {
    Direction dir = func->args[i].direction;
    if (dir != Direction::kOutput && dir != Direction::kInout) continue;
    if (SameArgValue(before[i], actuals[i])) continue;
    changes.push_back(DpiArgValueChange{i, before[i], actuals[i]});
  }
  return result;
}

DpiArgValue DpiRuntime::CallExport(std::string_view sv_name,
                                   const std::vector<DpiArgValue>& args) const {
  const auto* exp = FindExport(sv_name);
  if (!exp || !exp->impl) return DpiArgValue::FromInt(0);
  return exp->impl(args);
}

void DpiRuntime::PushScope(DpiScope scope) {
  scope_stack_.push_back(std::move(scope));
  current_scope_ = &scope_stack_.back();
}

void DpiRuntime::PopScope() {
  if (scope_stack_.empty()) return;
  scope_stack_.pop_back();
  current_scope_ = scope_stack_.empty() ? nullptr : &scope_stack_.back();
}

const DpiScope* DpiRuntime::CurrentScope() const { return current_scope_; }

void DpiRuntime::SetScope(const DpiScope* scope) { current_scope_ = scope; }

const DpiScope* DpiRuntime::GetScope() const { return current_scope_; }

uint32_t DpiRuntime::SvLow(const SvOpenArrayHandle&) { return 0; }

uint32_t DpiRuntime::SvHigh(const SvOpenArrayHandle& h) {
  return h.size > 0 ? h.size - 1 : 0;
}

uint32_t DpiRuntime::SvSize(const SvOpenArrayHandle& h) { return h.size; }

SvOpenArrayHandle DpiRuntime::MakeOpenArrayFromActual(void* actual_data,
                                                      uint32_t actual_size,
                                                      uint32_t elem_width) {
  // §35.6.1.1: the formal's unsized dimension takes the size of the
  // corresponding actual argument dimension; the element width is the type
  // information carried over from the import declaration. SvLow/SvHigh then
  // report the normalized range for the solitary unsized dimension.
  return SvOpenArrayHandle{actual_data, actual_size, elem_width};
}

void DpiRuntime::EnterContextImportCall(std::string_view sv_name,
                                        DpiScope decl_scope, bool is_task) {
  // §35.5.3: the chain's context is the import declaration's instantiated
  // scope when SystemVerilog calls a context import.
  PushScope(std::move(decl_scope));
  call_chain_.push_back({sv_name, true, is_task});
}

void DpiRuntime::EnterNoncontextImportCall(std::string_view sv_name,
                                           bool is_task) {
  call_chain_.push_back({sv_name, false, is_task});
}

void DpiRuntime::LeaveImportCall() {
  if (call_chain_.empty()) return;
  bool had_context = call_chain_.back().is_context;
  call_chain_.pop_back();
  if (had_context) PopScope();
}

uint32_t DpiRuntime::ImportCallDepth() const {
  return static_cast<uint32_t>(call_chain_.size());
}

bool DpiRuntime::ChainRootIsContext() const {
  if (call_chain_.empty()) return false;
  // §35.5.3: context property attaches to the *root* of the import chain,
  // never transitively promoted to subsequent inner calls.
  return call_chain_.front().is_context;
}

DpiExportCallStatus DpiRuntime::CallExportFromImport(
    std::string_view sv_name, const std::vector<DpiArgValue>& args,
    DpiArgValue* out_result) {
  const auto* exp = FindExport(sv_name);
  // §35.9 item d): once an imported subroutine has entered the disabled state,
  // it is illegal for the current call to make any further calls to exported
  // subroutines. This applies whatever the chain's context property or the kind
  // of export, so it is checked ahead of the §35.8 and §35.5.3 rules.
  if (DpiCurrentDisabledState()) {
    return DpiExportCallStatus::kDisabledStateExportCall;
  }
  // §35.8: it is never legal to call an exported task from within an imported
  // function — the DPI counterpart of the native rule that a function cannot
  // perform a task enable. When the innermost import in the chain is a function
  // and the export it is invoking names a task, reject the call outright,
  // independent of the chain's context property.
  if (!call_chain_.empty() && !call_chain_.back().is_task && exp != nullptr &&
      exp->is_task) {
    return DpiExportCallStatus::kFunctionCallsTask;
  }
  // §35.5.3: a noncontext DPI subroutine cannot call a SystemVerilog export.
  // The check looks at the *current* (innermost) import call's context
  // property, not the chain root, because context is not transitively
  // promoted.
  if (call_chain_.empty() || !call_chain_.back().is_context) {
    return DpiExportCallStatus::kNoncontextChain;
  }
  // §35.5.3: only exports declared in the chain's current scope can be
  // invoked directly. Calling an export defined in a different scope
  // requires the import to first set the chain scope via svSetScope.
  // When the export's scope_name is empty we treat the export as
  // scope-agnostic to keep callers that don't record scopes working.
  if (exp != nullptr && !exp->scope_name.empty() && current_scope_ != nullptr &&
      exp->scope_name != current_scope_->name) {
    return DpiExportCallStatus::kScopeMismatch;
  }
  // §35.5.3: when the export call returns, the chain context shall be the
  // value it had at the point the export was invoked. Snapshot and restore
  // around the call so that any scope changes performed by the export (or
  // by code it called) do not leak back to the import chain.
  const DpiScope* saved_scope = current_scope_;
  DpiArgValue result = CallExport(sv_name, args);
  current_scope_ = saved_scope;
  if (out_result) *out_result = result;
  return DpiExportCallStatus::kOk;
}

bool DpiRuntime::IsImportCallOptimizationBarrier(
    std::string_view sv_name) const {
  const auto* func = FindImport(sv_name);
  if (func == nullptr) return false;
  return func->is_context;
}

int DpiRuntime::ReturnFromExportUnderDisable(DpiDisableTarget target) {
  switch (target) {
    case DpiDisableTarget::kAncestor:
      // §35.9 item a): the exported task returns because a disable targets a
      // parent. The disable is still propagating, so the calling import enters
      // the disabled state and the task returns 1.
      DpiSetCurrentDisabledState(true);
      return 1;
    case DpiDisableTarget::kExportItself:
      // §35.9: when the exported task is itself the disable target, the disable
      // stops there — its parent import is not considered disabled, the task
      // returns 0, and svIsDisabledState() reports 0.
      DpiSetCurrentDisabledState(false);
      return 0;
    case DpiDisableTarget::kNone:
    default:
      // §35.9 item a): a task that does not return due to a disable returns 0.
      DpiSetCurrentDisabledState(false);
      return 0;
  }
}

bool DpiRuntime::IsDisabledState() const { return DpiCurrentDisabledState(); }

bool DpiRuntime::CheckImportedSubroutineDisableReturn(
    bool is_task, int task_return_value) const {
  // §35.9: the verification only applies to a subroutine returning while a
  // disable is in effect. With no disable there is nothing to check.
  if (!DpiCurrentDisabledState()) return true;
  if (is_task) {
    // item b): an imported task returning due to a disable shall return 1.
    return task_return_value == 1;
  }
  // item c): an imported function returning due to a disable shall have
  // acknowledged it by calling svAckDisabledState() first.
  return DpiCurrentDisableAcknowledged();
}

void CoverageApi::SetControl(CoverageControl ctrl) { control_ = ctrl; }
CoverageControl CoverageApi::GetControl() const { return control_; }

void CoverageApi::SetMaxBins(uint32_t max_bins) { max_bins_ = max_bins; }
uint32_t CoverageApi::GetMaxBins() const { return max_bins_; }

void CoverageApi::SetActive(bool active) { active_ = active; }
bool CoverageApi::IsActive() const { return active_; }

void CoverageApi::StoreValue(std::string_view key, double value) {
  values_[std::string(key)] = value;
}

double CoverageApi::GetValue(std::string_view key) const {
  auto it = values_.find(std::string(key));
  if (it == values_.end()) return 0.0;
  return it->second;
}

void DataReadApi::StoreVariable(std::string_view name,
                                const DataReadValue& val) {
  variables_[std::string(name)] = val;
}

DataReadValue DataReadApi::GetValue(std::string_view name,
                                    DataReadFormat fmt) const {
  auto it = variables_.find(std::string(name));
  if (it == variables_.end()) return DataReadValue{fmt, 0, 0.0, "", 0, {}};
  DataReadValue result = it->second;
  result.format = fmt;
  return result;
}

void DataReadApi::PutValue(std::string_view name, const DataReadValue& val) {
  variables_[std::string(name)] = val;
  NotifyValueChange(name, val);
}

void DataReadApi::RegisterValueChangeCb(std::string_view name,
                                        ValueChangeCb cb) {
  change_cbs_[std::string(name)].push_back(std::move(cb));
}

void DataReadApi::NotifyValueChange(std::string_view name,
                                    const DataReadValue& val) {
  auto it = change_cbs_.find(std::string(name));
  if (it == change_cbs_.end()) return;
  for (auto& cb : it->second) {
    cb(name, val);
  }
}

uint32_t DataReadApi::ValueChangeCbCount() const {
  uint32_t total = 0;
  for (const auto& [key, cbs] : change_cbs_) {
    total += static_cast<uint32_t>(cbs.size());
  }
  return total;
}

}  // namespace delta
