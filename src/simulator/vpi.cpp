#include <cstdarg>
#include <cstddef>
#include <cstdio>
#include <ostream>
#include <string>
#include <string_view>
#include <unordered_map>
#include <utility>

#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_assertion_cb.h"
#include "simulator/vpi_assertion_control.h"
#include "simulator/vpi_channel_state.h"
#include "simulator/vpi_constants.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_data_structs.h"
#include "simulator/vpi_globals.h"
#include "simulator/vpi_internal.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_routine_error_scope.h"
#include "simulator/vpi_run_files.h"
#include "simulator/vpi_user.h"

namespace {

using delta::VpiRoutineErrorScope;

vpiHandle HandOut(delta::VpiObject* object) {
  if (object != nullptr) {
    ++object->handles_held;
    object->released = false;
  }
  return delta::VpiHandleOf(object);
}

}  // namespace

vpiHandle vpi_register_systf(s_vpi_systf_data* data) {
  VpiRoutineErrorScope error_scope;
  return delta::VpiHandleOf(delta::GetGlobalVpiContext().RegisterSystf(data));
}

void vpi_get_systf_info(vpiHandle obj, s_vpi_systf_data* systf_data_p) {
  VpiRoutineErrorScope error_scope;
  delta::GetGlobalVpiContext().GetSystfInfo(delta::VpiObjectOf(obj),
                                            systf_data_p);
}

void vpi_get_cb_info(vpiHandle obj, s_cb_data* cb_data_p) {
  VpiRoutineErrorScope error_scope;
  delta::GetGlobalVpiContext().GetCbInfo(delta::VpiObjectOf(obj), cb_data_p);
}

void vpi_get_time(vpiHandle obj, s_vpi_time* time_p) {
  VpiRoutineErrorScope error_scope;
  delta::GetGlobalVpiContext().GetTime(delta::VpiObjectOf(obj), time_p);
}

void vpi_get_delays(vpiHandle obj, p_vpi_delay delay_p) {
  VpiRoutineErrorScope error_scope;
  delta::GetGlobalVpiContext().GetDelays(delta::VpiObjectOf(obj), delay_p);
}

void vpi_put_delays(vpiHandle obj, p_vpi_delay delay_p) {
  VpiRoutineErrorScope error_scope;
  delta::GetGlobalVpiContext().PutDelays(delta::VpiObjectOf(obj), delay_p);
}

PLI_INT32 vpi_get_data(PLI_INT32 id, PLI_BYTE8* data_loc,
                       PLI_INT32 num_of_bytes) {
  VpiRoutineErrorScope error_scope;
  return delta::GetGlobalVpiContext().GetData(id, data_loc, num_of_bytes);
}

PLI_INT32 vpi_put_data(PLI_INT32 id, PLI_BYTE8* data_loc,
                       PLI_INT32 num_of_bytes) {
  VpiRoutineErrorScope error_scope;
  return delta::GetGlobalVpiContext().PutData(id, data_loc, num_of_bytes);
}

PLI_INT32 vpi_put_userdata(vpiHandle obj, void* userdata) {
  VpiRoutineErrorScope error_scope;
  return delta::GetGlobalVpiContext().PutUserData(delta::VpiObjectOf(obj),
                                                  userdata);
}

void* vpi_get_userdata(vpiHandle obj) {
  VpiRoutineErrorScope error_scope;
  return delta::GetGlobalVpiContext().GetUserData(delta::VpiObjectOf(obj));
}

vpiHandle vpi_handle(PLI_INT32 type, vpiHandle ref) {
  VpiRoutineErrorScope error_scope;
  return HandOut(
      delta::GetGlobalVpiContext().Handle(type, delta::VpiObjectOf(ref)));
}

vpiHandle vpi_handle_by_name(PLI_BYTE8* name, vpiHandle scope) {
  VpiRoutineErrorScope error_scope;
  return HandOut(delta::GetGlobalVpiContext().HandleByName(
      name, delta::VpiObjectOf(scope)));
}

vpiHandle vpi_handle_by_index(vpiHandle parent, PLI_INT32 index) {
  VpiRoutineErrorScope error_scope;
  return HandOut(delta::GetGlobalVpiContext().HandleByIndex(
      index, delta::VpiObjectOf(parent)));
}

vpiHandle vpi_handle_by_multi_index(vpiHandle parent, PLI_INT32 num_index,
                                    PLI_INT32* index_array) {
  VpiRoutineErrorScope error_scope;
  return HandOut(delta::GetGlobalVpiContext().HandleByMultiIndex(
      num_index, index_array, delta::VpiObjectOf(parent)));
}

vpiHandle vpi_handle_multi(PLI_INT32 type, vpiHandle ref1, vpiHandle ref2,
                           ...) {
  VpiRoutineErrorScope error_scope;
  return HandOut(delta::GetGlobalVpiContext().HandleMulti(
      type, delta::VpiObjectOf(ref1), delta::VpiObjectOf(ref2)));
}

PLI_INT32 vpi_compare_objects(vpiHandle obj1, vpiHandle obj2) {
  VpiRoutineErrorScope error_scope;
  return delta::GetGlobalVpiContext().CompareObjects(delta::VpiObjectOf(obj1),
                                                     delta::VpiObjectOf(obj2));
}

vpiHandle vpi_iterate(PLI_INT32 type, vpiHandle ref) {
  VpiRoutineErrorScope error_scope;
  return delta::VpiHandleOf(delta::VpiIterateInCompatibilityMode(
      type, delta::VpiObjectOf(ref),
      delta::GetGlobalVpiContext().EffectiveCompatibilityMode(false, 0)));
}

vpiHandle vpi_scan(vpiHandle iterator) {
  VpiRoutineErrorScope error_scope;
  return HandOut(
      delta::GetGlobalVpiContext().Scan(delta::VpiObjectOf(iterator)));
}

void vpi_get_value(vpiHandle obj, s_vpi_value* value) {
  VpiRoutineErrorScope error_scope;
  if (delta::GetGlobalVpiContext().RoutineIsUnavailableNow(
          delta::VpiRoutine::kGetValue)) {
    return;
  }
  delta::GetGlobalVpiContext().GetValue(delta::VpiObjectOf(obj), value);
}

vpiHandle vpi_put_value(vpiHandle obj, s_vpi_value* value, s_vpi_time* time,
                        PLI_INT32 flags) {
  VpiRoutineErrorScope error_scope;
  if (delta::GetGlobalVpiContext().RoutineIsUnavailableNow(
          delta::VpiRoutine::kPutValue)) {
    return nullptr;
  }
  return delta::VpiHandleOf(delta::GetGlobalVpiContext().PutValue(
      delta::VpiObjectOf(obj), value, time, flags));
}

void vpi_put_value_array(vpiHandle obj, p_vpi_arrayvalue arrayvalue_p,
                         PLI_INT32* index_p, PLI_UINT32 num) {
  VpiRoutineErrorScope error_scope;
  delta::GetGlobalVpiContext().PutValueArray(delta::VpiObjectOf(obj),
                                             arrayvalue_p, index_p, num);
}

void vpi_get_value_array(vpiHandle obj, p_vpi_arrayvalue arrayvalue_p,
                         PLI_INT32* index_p, PLI_UINT32 num) {
  VpiRoutineErrorScope error_scope;
  delta::GetGlobalVpiContext().GetValueArray(delta::VpiObjectOf(obj),
                                             arrayvalue_p, index_p, num);
}

vpiHandle vpi_register_cb(s_cb_data* data) {
  VpiRoutineErrorScope error_scope;
  return delta::VpiHandleOf(delta::GetGlobalVpiContext().RegisterCb(data));
}

PLI_INT32 vpi_remove_cb(vpiHandle cb_handle) {
  VpiRoutineErrorScope error_scope;
  if (delta::VpiRemoveAssertionCb(delta::VpiObjectOf(cb_handle))) return 1;
  return delta::GetGlobalVpiContext().RemoveCb(delta::VpiObjectOf(cb_handle));
}

PLI_INT32 vpi_get(PLI_INT32 property, vpiHandle obj) {
  VpiRoutineErrorScope error_scope;
  return delta::VpiGetInCompatibilityMode(
      property, delta::VpiObjectOf(obj),
      delta::GetGlobalVpiContext().EffectiveCompatibilityMode(false, 0));
}

PLI_INT64 vpi_get64(PLI_INT32 property, vpiHandle obj) {
  VpiRoutineErrorScope error_scope;
  return delta::GetGlobalVpiContext().Get64(property, delta::VpiObjectOf(obj));
}

PLI_BYTE8* vpi_get_str(PLI_INT32 property, vpiHandle obj) {
  VpiRoutineErrorScope error_scope;
  return delta::GetGlobalVpiContext().GetStr(property, delta::VpiObjectOf(obj));
}

PLI_INT32 vpi_free_object(vpiHandle obj) {
  VpiRoutineErrorScope error_scope;
  return delta::GetGlobalVpiContext().FreeObject(delta::VpiObjectOf(obj));
}

PLI_INT32 vpi_release_handle(vpiHandle obj) {
  VpiRoutineErrorScope error_scope;
  return delta::GetGlobalVpiContext().ReleaseHandleStatus(
      delta::VpiObjectOf(obj));
}

static PLI_INT32 VpiAssertionControlWithArgs(PLI_INT32 operation, va_list args,
                                             bool* handled) {
  *handled = true;
  if (delta::VpiIsAssertionSysControl(operation)) {
    vpiHandle scope = va_arg(args, vpiHandle);
    return delta::VpiAssertionSysControl(operation, delta::VpiObjectOf(scope));
  }
  if (delta::VpiIsAssertionControl(operation)) {
    vpiHandle assertion = va_arg(args, vpiHandle);
    return delta::VpiAssertionControl(operation, delta::VpiObjectOf(assertion));
  }
  if (delta::VpiIsAssertionAttemptControl(operation)) {
    vpiHandle assertion = va_arg(args, vpiHandle);
    s_vpi_time* attempt = va_arg(args, s_vpi_time*);
    return delta::VpiAssertionAttemptControl(
        operation, delta::VpiObjectOf(assertion), attempt);
  }
  if (delta::VpiIsAssertionStepControl(operation)) {
    vpiHandle assertion = va_arg(args, vpiHandle);
    s_vpi_time* attempt = va_arg(args, s_vpi_time*);
    int step_control = va_arg(args, int);
    return delta::VpiAssertionStepControl(
        operation, delta::VpiObjectOf(assertion), attempt, step_control);
  }
  *handled = false;
  return 0;
}

PLI_INT32 VpiControlWithArgs(PLI_INT32 operation, va_list args) {
  int result = 0;
  bool handled = false;
  switch (operation) {
    case delta::kVpiStop:
    case delta::kVpiFinish: {
      int diag_level = va_arg(args, int);
      result = delta::GetGlobalVpiContext().Control(operation, diag_level);
      break;
    }
    case delta::kVpiSetInteractiveScope: {
      vpiHandle scope = va_arg(args, vpiHandle);
      result = delta::GetGlobalVpiContext().Control(operation, 0,
                                                    delta::VpiObjectOf(scope));
      break;
    }
    case vpiCoverageStart:
    case vpiCoverageStop:
    case vpiCoverageReset:
    case vpiCoverageCheck: {
      int coverage_type = va_arg(args, int);
      vpiHandle handle = va_arg(args, vpiHandle);
      result = delta::GetGlobalVpiContext().ControlCoverage(
          operation, coverage_type, delta::VpiObjectOf(handle), std::string());
      break;
    }
    case vpiCoverageSave:
    case vpiCoverageMerge: {
      int coverage_type = va_arg(args, int);
      const char* name = va_arg(args, const char*);
      result = delta::GetGlobalVpiContext().ControlCoverage(
          operation, coverage_type, nullptr,
          name ? std::string(name) : std::string());
      break;
    }
    default:
      result = VpiAssertionControlWithArgs(operation, args, &handled);
      if (!handled) result = delta::GetGlobalVpiContext().Control(operation);
      break;
  }
  return result;
}

PLI_INT32 vpi_control(PLI_INT32 operation, ...) {
  VpiRoutineErrorScope error_scope;
  va_list args;
  va_start(args, operation);
  PLI_INT32 result = VpiControlWithArgs(operation, args);
  va_end(args);
  return result;
}

PLI_INT32 vpi_chk_error(s_vpi_error_info* info) {
  auto& ctx = delta::GetGlobalVpiContext();
  ctx.ChkError(info);
  return ctx.LastError().level;
}

PLI_INT32 vpi_get_vlog_info(s_vpi_vlog_info* info) {
  VpiRoutineErrorScope error_scope;
  return delta::GetGlobalVpiContext().GetVlogInfo(info) ? 1 : 0;
}

namespace delta {

void VpiContext::WriteOutputChannel(std::string_view text) {
  if (channels_.run_output != nullptr) {
    *channels_.run_output << text;
    return;
  }
  channels_.output_channel_buffer.append(text);
}

void VpiContext::WriteLogFile(std::string_view text) {
  if (channels_.run_output != nullptr) return;
  channels_.log_file_buffer.append(text);
}

void VpiContext::ConnectOutputChannel(std::ostream* out) {
  channels_.run_output = out;
  if (out == nullptr) return;
  *out << channels_.output_channel_flushed << channels_.output_channel_buffer;
  channels_.output_channel_flushed.clear();
  channels_.output_channel_buffer.clear();
  channels_.log_file_flushed.clear();
  channels_.log_file_buffer.clear();
}

int VpiContext::Flush() {
  if (channels_.flush_should_fail) return 1;
  if (channels_.run_output != nullptr) channels_.run_output->flush();
  channels_.output_channel_flushed.append(channels_.output_channel_buffer);
  channels_.output_channel_buffer.clear();
  channels_.log_file_flushed.append(channels_.log_file_buffer);
  channels_.log_file_buffer.clear();
  return 0;
}

constexpr PLI_UINT32 kVpiFdDescriptorChannel = PLI_UINT32{1} << 31;

constexpr PLI_UINT32 kVpiToolOutputChannel = 1;

const std::string& VpiContext::McdChannelBuffer(PLI_UINT32 channel) const {
  auto it = channels_.mcd_channel_buffers.find(channel);
  return it == channels_.mcd_channel_buffers.end() ? channels_.empty_mcd_buffer
                                                   : it->second;
}

const std::string& VpiContext::McdChannelFlushed(PLI_UINT32 channel) const {
  auto it = channels_.mcd_channel_flushed.find(channel);
  return it == channels_.mcd_channel_flushed.end() ? channels_.empty_mcd_buffer
                                                   : it->second;
}

void VpiContext::WriteMcdChannel(PLI_UINT32 channel, std::string_view text) {
  if (channel == kVpiToolOutputChannel) {
    WriteOutputChannel(text);
    WriteLogFile(text);
    return;
  }
  if (sim_ctx_ != nullptr) {
    VpiRunMcdWrite(*sim_ctx_, channel, text);
    return;
  }
  channels_.mcd_channel_buffers[channel].append(text);
}

PLI_UINT32 VpiContext::McdOpen(const std::string& filename) {
  if (sim_ctx_ != nullptr) return VpiRunMcdOpen(*sim_ctx_, filename);

  auto existing = channels_.mcd_open_files.find(filename);
  const bool kOpenAsMcd = existing != channels_.mcd_open_files.end() &&
                          (existing->second & kVpiFdDescriptorChannel) == 0;
  if (kOpenAsMcd) return existing->second;

  if (channels_.mcd_open_should_fail) return 0;

  for (int bit = 1; bit <= 30; ++bit) {
    PLI_UINT32 channel = PLI_UINT32{1} << bit;
    if ((channels_.mcd_allocated_channels & channel) != 0) continue;
    channels_.mcd_allocated_channels |= channel;
    channels_.mcd_open_files[filename] = channel;
    return channel;
  }

  return 0;
}

namespace {

void CloseMcdChannelFiles(
    std::unordered_map<std::string, PLI_UINT32>& open_files,
    PLI_UINT32 channel) {
  for (auto it = open_files.begin(); it != open_files.end();) {
    if ((it->second & channel) != 0) {
      it->second &= ~channel;
      if (it->second == 0) {
        it = open_files.erase(it);
        continue;
      }
    }
    ++it;
  }
}

bool CloseMcdChannelBit(int bit, PLI_UINT32 mcd, VpiChannelState& channels) {
  PLI_UINT32& allocated_channels = channels.mcd_allocated_channels;
  PLI_UINT32 channel = PLI_UINT32{1} << bit;
  if ((mcd & channel) == 0) return false;

  if (bit == 0) return true;

  if ((allocated_channels & channel) == 0) return true;

  allocated_channels &= ~channel;
  CloseMcdChannelFiles(channels.mcd_open_files, channel);
  return false;
}

void FlushMcdChannel(VpiChannelState& channels, PLI_UINT32 channel) {
  auto it = channels.mcd_channel_buffers.find(channel);
  if (it == channels.mcd_channel_buffers.end()) return;
  channels.mcd_channel_flushed[channel].append(it->second);
  it->second.clear();
}

PLI_UINT32 CloseMcdFd(PLI_UINT32 fd,
                      std::unordered_map<std::string, PLI_UINT32>& open_files) {
  for (auto it = open_files.begin(); it != open_files.end(); ++it) {
    if (it->second == fd) {
      open_files.erase(it);
      return 0;
    }
  }
  return fd;
}

}  // namespace

PLI_UINT32 VpiContext::McdClose(PLI_UINT32 mcd) {
  if (sim_ctx_ != nullptr) return VpiRunMcdClose(*sim_ctx_, mcd);

  if ((mcd & kVpiFdDescriptorChannel) != 0) {
    return CloseMcdFd(mcd, channels_.mcd_open_files);
  }

  PLI_UINT32 unclosed = 0;
  for (int bit = 0; bit < 32; ++bit) {
    if (CloseMcdChannelBit(bit, mcd, channels_)) {
      unclosed |= PLI_UINT32{1} << bit;
    }
  }

  return unclosed;
}

PLI_INT32 VpiContext::McdFlush(PLI_UINT32 mcd) {
  if (channels_.mcd_flush_should_fail) return 1;

  for (int bit = 0; bit < 32; ++bit) {
    PLI_UINT32 channel = PLI_UINT32{1} << bit;
    if ((mcd & channel) == 0) continue;
    if (channel == kVpiToolOutputChannel) {
      if (Flush() != 0) return 1;
      continue;
    }
    if (sim_ctx_ != nullptr) {
      if (!VpiRunMcdFlush(*sim_ctx_, channel)) return 1;
      continue;
    }
    FlushMcdChannel(channels_, channel);
  }

  return 0;
}

PLI_BYTE8* VpiContext::McdName(PLI_UINT32 cd) {
  if (cd == 0) return nullptr;

  const bool kSingleChannel =
      (cd & kVpiFdDescriptorChannel) != 0 || (cd & (cd - 1)) == 0;
  if (!kSingleChannel) return nullptr;

  const std::string* name = nullptr;
  if (sim_ctx_ != nullptr) name = VpiRunFileName(*sim_ctx_, cd);
  for (const auto& [opened, descriptor] : channels_.mcd_open_files) {
    if (descriptor == cd) name = &opened;
  }
  if (name != nullptr) {
    if (channels_.mcd_name_buffer.capacity() < 256)
      channels_.mcd_name_buffer.reserve(256);
    channels_.mcd_name_buffer.assign(*name);
    return channels_.mcd_name_buffer.data();
  }

  return nullptr;
}

PLI_INT32 VpiContext::McdPrintf(PLI_UINT32 mcd, std::string_view text) {
  if ((mcd & kVpiFdDescriptorChannel) != 0) return 0;

  for (int bit = 0; bit < 31; ++bit) {
    PLI_UINT32 channel = PLI_UINT32{1} << bit;
    if ((mcd & channel) == 0) continue;
    WriteMcdChannel(channel, text);
  }

  return static_cast<PLI_INT32>(text.size());
}

PLI_INT32 VpiContext::Printf(std::string_view text) {
  WriteOutputChannel(text);
  WriteLogFile(text);

  return static_cast<PLI_INT32>(text.size());
}

static bool FormatVaList(const char* format, va_list args, std::string& out) {
  va_list measure;
  va_copy(measure, args);
  int needed = std::vsnprintf(nullptr, 0, format, measure);
  va_end(measure);
  if (needed < 0) {
    return false;
  }
  std::string text(static_cast<std::size_t>(needed), '\0');
  if (needed > 0) {
    std::vsnprintf(text.data(), static_cast<std::size_t>(needed) + 1, format,
                   args);
  }
  out = std::move(text);
  return true;
}

}  // namespace delta

PLI_INT32 vpi_flush() {
  VpiRoutineErrorScope error_scope;
  return delta::GetGlobalVpiContext().Flush();
}

PLI_UINT32 vpi_mcd_open(PLI_BYTE8* file) {
  VpiRoutineErrorScope error_scope;
  if (file == nullptr) return 0;
  return delta::GetGlobalVpiContext().McdOpen(file);
}

PLI_UINT32 vpi_mcd_close(PLI_UINT32 mcd) {
  VpiRoutineErrorScope error_scope;
  return delta::GetGlobalVpiContext().McdClose(mcd);
}

PLI_INT32 vpi_mcd_flush(PLI_UINT32 mcd) {
  VpiRoutineErrorScope error_scope;
  return delta::GetGlobalVpiContext().McdFlush(mcd);
}

PLI_BYTE8* vpi_mcd_name(PLI_UINT32 cd) {
  VpiRoutineErrorScope error_scope;
  return delta::GetGlobalVpiContext().McdName(cd);
}

PLI_INT32 vpi_mcd_printf(PLI_UINT32 mcd, PLI_BYTE8* format, ...) {
  VpiRoutineErrorScope error_scope;

  if (format == nullptr) return EOF;

  va_list args;
  va_start(args, format);
  std::string text;
  bool ok = delta::FormatVaList(format, args, text);
  va_end(args);
  if (!ok) {
    return EOF;
  }

  return delta::GetGlobalVpiContext().McdPrintf(mcd, text);
}

PLI_INT32 vpi_mcd_vprintf(PLI_UINT32 mcd, PLI_BYTE8* format, va_list ap) {
  VpiRoutineErrorScope error_scope;

  if (format == nullptr) return EOF;

  std::string text;
  if (!delta::FormatVaList(format, ap, text)) {
    return EOF;
  }

  return delta::GetGlobalVpiContext().McdPrintf(mcd, text);
}

PLI_INT32 vpi_printf(PLI_BYTE8* format, ...) {
  VpiRoutineErrorScope error_scope;

  if (format == nullptr) return EOF;

  va_list args;
  va_start(args, format);
  std::string text;
  bool ok = delta::FormatVaList(format, args, text);
  va_end(args);
  if (!ok) {
    return EOF;
  }

  return delta::GetGlobalVpiContext().Printf(text);
}

PLI_INT32 vpi_vprintf(PLI_BYTE8* format, va_list ap) {
  VpiRoutineErrorScope error_scope;

  if (format == nullptr) return EOF;

  std::string text;
  if (!delta::FormatVaList(format, ap, text)) {
    return EOF;
  }

  return delta::GetGlobalVpiContext().Printf(text);
}
