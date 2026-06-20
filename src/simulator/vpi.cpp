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

vpiHandle vpi_register_systf(s_vpi_systf_data* data) {
  delta::GetGlobalVpiContext().ResetErrorStatus();  // §38.2: clear prior error
  return delta::GetGlobalVpiContext().RegisterSystf(data);
}

void vpi_get_systf_info(vpiHandle obj, s_vpi_systf_data* systf_data_p) {
  delta::GetGlobalVpiContext().ResetErrorStatus();  // §38.2: clear prior error
  delta::GetGlobalVpiContext().GetSystfInfo(obj, systf_data_p);
}

void vpi_get_cb_info(vpiHandle obj, s_cb_data* cb_data_p) {
  delta::GetGlobalVpiContext().ResetErrorStatus();  // §38.2: clear prior error
  delta::GetGlobalVpiContext().GetCbInfo(obj, cb_data_p);
}

void vpi_get_time(vpiHandle obj, s_vpi_time* time_p) {
  delta::GetGlobalVpiContext().ResetErrorStatus();  // §38.2: clear prior error
  delta::GetGlobalVpiContext().GetTime(obj, time_p);
}

void vpi_get_delays(vpiHandle obj, p_vpi_delay delay_p) {
  delta::GetGlobalVpiContext().ResetErrorStatus();  // §38.2: clear prior error
  delta::GetGlobalVpiContext().GetDelays(obj, delay_p);
}

void vpi_put_delays(vpiHandle obj, p_vpi_delay delay_p) {
  delta::GetGlobalVpiContext().ResetErrorStatus();  // §38.2: clear prior error
  delta::GetGlobalVpiContext().PutDelays(obj, delay_p);
}

PLI_INT32 vpi_get_data(PLI_INT32 id, PLI_BYTE8* dataLoc, PLI_INT32 numOfBytes) {
  delta::GetGlobalVpiContext().ResetErrorStatus();  // §38.2: clear prior error
  return delta::GetGlobalVpiContext().GetData(id, dataLoc, numOfBytes);
}

PLI_INT32 vpi_put_data(PLI_INT32 id, PLI_BYTE8* dataLoc, PLI_INT32 numOfBytes) {
  delta::GetGlobalVpiContext().ResetErrorStatus();  // §38.2: clear prior error
  return delta::GetGlobalVpiContext().PutData(id, dataLoc, numOfBytes);
}

PLI_INT32 vpi_put_userdata(vpiHandle obj, void* userdata) {
  delta::GetGlobalVpiContext().ResetErrorStatus();  // §38.2: clear prior error
  return delta::GetGlobalVpiContext().PutUserData(obj, userdata);
}

void* vpi_get_userdata(vpiHandle obj) {
  delta::GetGlobalVpiContext().ResetErrorStatus();  // §38.2: clear prior error
  return delta::GetGlobalVpiContext().GetUserData(obj);
}

vpiHandle VpiHandleC(int type, vpiHandle ref) {
  delta::GetGlobalVpiContext().ResetErrorStatus();  // §38.2: clear prior error
  return delta::GetGlobalVpiContext().Handle(type, ref);
}

vpiHandle vpi_handle_by_name(const char* name, vpiHandle scope) {
  delta::GetGlobalVpiContext().ResetErrorStatus();  // §38.2: clear prior error
  return delta::GetGlobalVpiContext().HandleByName(name, scope);
}

vpiHandle VpiHandleByIndexC(vpiHandle parent, int index) {
  delta::GetGlobalVpiContext().ResetErrorStatus();  // §38.2: clear prior error
  return delta::GetGlobalVpiContext().HandleByIndex(index, parent);
}

vpiHandle VpiHandleByMultiIndexC(vpiHandle parent, int num_index,
                                 int* index_array) {
  delta::GetGlobalVpiContext().ResetErrorStatus();  // §38.2: clear prior error
  return delta::GetGlobalVpiContext().HandleByMultiIndex(num_index, index_array,
                                                         parent);
}

vpiHandle VpiHandleMultiC(int type, vpiHandle ref1, vpiHandle ref2) {
  delta::GetGlobalVpiContext().ResetErrorStatus();  // §38.2: clear prior error
  return delta::GetGlobalVpiContext().HandleMulti(type, ref1, ref2);
}

int VpiCompareObjectsC(vpiHandle obj1, vpiHandle obj2) {
  delta::GetGlobalVpiContext().ResetErrorStatus();  // §38.2: clear prior error
  return delta::GetGlobalVpiContext().CompareObjects(obj1, obj2);
}

vpiHandle vpi_iterate(int type, vpiHandle ref) {
  delta::GetGlobalVpiContext().ResetErrorStatus();  // §38.2: clear prior error
  return delta::GetGlobalVpiContext().Iterate(type, ref);
}

vpiHandle vpi_scan(vpiHandle iterator) {
  delta::GetGlobalVpiContext().ResetErrorStatus();  // §38.2: clear prior error
  return delta::GetGlobalVpiContext().Scan(iterator);
}

void vpi_get_value(vpiHandle obj, s_vpi_value* value) {
  delta::GetGlobalVpiContext().ResetErrorStatus();  // §38.2: clear prior error
  delta::GetGlobalVpiContext().GetValue(obj, value);
}

vpiHandle vpi_put_value(vpiHandle obj, s_vpi_value* value, s_vpi_time* time,
                        int flags) {
  delta::GetGlobalVpiContext().ResetErrorStatus();  // §38.2: clear prior error
  return delta::GetGlobalVpiContext().PutValue(obj, value, time, flags);
}

void vpi_put_value_array(vpiHandle obj, p_vpi_arrayvalue arrayvalue_p,
                         PLI_INT32* index_p, PLI_UINT32 num) {
  delta::GetGlobalVpiContext().ResetErrorStatus();  // §38.2: clear prior error
  delta::GetGlobalVpiContext().PutValueArray(obj, arrayvalue_p, index_p, num);
}

void vpi_get_value_array(vpiHandle obj, p_vpi_arrayvalue arrayvalue_p,
                         PLI_INT32* index_p, PLI_UINT32 num) {
  delta::GetGlobalVpiContext().ResetErrorStatus();  // §38.2: clear prior error
  delta::GetGlobalVpiContext().GetValueArray(obj, arrayvalue_p, index_p, num);
}

vpiHandle vpi_register_cb(s_cb_data* data) {
  delta::GetGlobalVpiContext().ResetErrorStatus();  // §38.2: clear prior error
  return delta::GetGlobalVpiContext().RegisterCb(data);
}

int VpiRemoveCbC(vpiHandle cb_handle) {
  delta::GetGlobalVpiContext().ResetErrorStatus();  // §38.2: clear prior error
  return delta::GetGlobalVpiContext().RemoveCb(cb_handle);
}

int vpi_get(int property, vpiHandle obj) {
  delta::GetGlobalVpiContext().ResetErrorStatus();  // §38.2: clear prior error
  return delta::GetGlobalVpiContext().Get(property, obj);
}

PLI_INT64 vpi_get64(int property, vpiHandle obj) {
  delta::GetGlobalVpiContext().ResetErrorStatus();  // §38.2: clear prior error
  return delta::GetGlobalVpiContext().Get64(property, obj);
}

const char* vpi_get_str(int property, vpiHandle obj) {
  delta::GetGlobalVpiContext().ResetErrorStatus();  // §38.2: clear prior error
  return delta::GetGlobalVpiContext().GetStr(property, obj);
}

int vpi_free_object(vpiHandle obj) {
  delta::GetGlobalVpiContext().ResetErrorStatus();  // §38.2: clear prior error
  return delta::GetGlobalVpiContext().FreeObject(obj);
}

PLI_INT32 vpi_release_handle(vpiHandle obj) {
  delta::GetGlobalVpiContext().ResetErrorStatus();  // §38.2: clear prior error
  return delta::GetGlobalVpiContext().ReleaseHandleStatus(obj);
}

int VpiControlC(int operation, ...) {
  // §38.4: vpi_control(operation, varargs) takes a variable number of
  // operation-specific arguments. Read exactly the arguments the operation
  // defines before forwarding the request to the simulator.
  delta::GetGlobalVpiContext().ResetErrorStatus();  // §38.2: clear prior error
  va_list args;
  va_start(args, operation);
  int result = 0;
  switch (operation) {
    case delta::kVpiStop:
    case delta::kVpiFinish: {
      int diag_level = va_arg(args, int);
      result = delta::GetGlobalVpiContext().Control(operation, diag_level);
      break;
    }
    case delta::kVpiReset: {
      int stop_value = va_arg(args, int);
      int reset_value = va_arg(args, int);
      int diag_value = va_arg(args, int);
      result = delta::GetGlobalVpiContext().Control(operation, stop_value,
                                                    reset_value, diag_value);
      break;
    }
    case delta::kVpiSetInteractiveScope: {
      vpiHandle scope = va_arg(args, vpiHandle);
      result = delta::GetGlobalVpiContext().Control(operation, 0, 0, 0, scope);
      break;
    }
    case vpiCoverageStart:
    case vpiCoverageStop:
    case vpiCoverageReset:
    case vpiCoverageCheck: {
      // §40.5.3: vpi_control(<coverageControl>, <coverageType>, handle)
      // controls the collection of coverage over the instance or assertion the
      // handle names. The coverage type is the second argument and the
      // controlled scope is the third.
      int coverage_type = va_arg(args, int);
      vpiHandle handle = va_arg(args, vpiHandle);
      result = delta::GetGlobalVpiContext().ControlCoverage(
          operation, coverage_type, handle, std::string());
      break;
    }
    case vpiCoverageSave:
    case vpiCoverageMerge: {
      // §40.5.3: vpi_control(<coverageControl>, <coverageType>, name) saves or
      // merges coverage of the requested type against the coverage database
      // located by the name string given as the third argument.
      int coverage_type = va_arg(args, int);
      const char* name = va_arg(args, const char*);
      result = delta::GetGlobalVpiContext().ControlCoverage(
          operation, coverage_type, nullptr,
          name ? std::string(name) : std::string());
      break;
    }
    default:
      result = delta::GetGlobalVpiContext().Control(operation);
      break;
  }
  va_end(args);
  return result;
}

int VpiChkErrorC(SVpiErrorInfo* info) {
  // §38.2: vpi_chk_error() returns the severity level (a Table 38-1 constant)
  // of the error left by the previous VPI routine call, or 0 (false) when that
  // call did not result in an error. When info is non-null the error detail is
  // copied out. Unlike every other VPI routine, vpi_chk_error() does not reset
  // the error status, so the level it reports survives a repeated query.
  auto& ctx = delta::GetGlobalVpiContext();
  ctx.ChkError(info);
  return ctx.LastError().level;
}

PLI_INT32 vpi_get_vlog_info(SVpiVlogInfo* info) {
  delta::GetGlobalVpiContext().ResetErrorStatus();  // §38.2: clear prior error
  // §38.17: return 1 (true) on success and 0 (false) when the information
  // cannot be supplied.
  return delta::GetGlobalVpiContext().GetVlogInfo(info) ? 1 : 0;
}

namespace delta {

int VpiContext::Flush() {
  // §38.5: flush the buffered output of both the simulator's output channel and
  // the current log file. Committing each buffer into its committed stream and
  // clearing it is the observable effect of forcing the buffered text out. If
  // the underlying flush cannot complete, report failure and leave the buffers
  // intact so nothing is lost.
  if (flush_should_fail_) return 1;
  output_channel_flushed_.append(output_channel_buffer_);
  output_channel_buffer_.clear();
  log_file_flushed_.append(log_file_buffer_);
  log_file_buffer_.clear();
  return 0;
}

PLI_UINT32 VpiContext::McdOpen(const std::string& filename) {
  // §38.27: a file already open in the shared mcd namespace - whether a prior
  // vpi_mcd_open() assigned it or $fopen seeded it - is reported on the very
  // descriptor it already holds, rather than consuming a second channel.
  auto existing = mcd_open_files_.find(filename);
  if (existing != mcd_open_files_.end()) return existing->second;

  // §38.27: an open that cannot be carried out returns 0.
  if (mcd_open_should_fail_) return 0;

  // §38.27: pick a free channel. Channel 1 (bit 0, the LSB) is reserved for the
  // tool's output channel and log file, and channel 32 (bit 31, the MSB) is
  // reserved to stand for an fd from $fopen, so a fresh descriptor is drawn
  // only from channels 2..31 (bits 1..30). The chosen channel is the single bit
  // set in the returned mcd.
  for (int bit = 1; bit <= 30; ++bit) {
    PLI_UINT32 channel = PLI_UINT32{1} << bit;
    if ((mcd_allocated_channels_ & channel) != 0) continue;
    // §38.27: open the file for writing and hand back its multichannel
    // descriptor, recording it so a later open of the same file finds it.
    mcd_allocated_channels_ |= channel;
    mcd_open_files_.emplace(filename, channel);
    return channel;
  }

  // §38.27: no channel was free, so the open fails and returns 0.
  return 0;
}

PLI_UINT32 VpiContext::McdClose(PLI_UINT32 mcd) {
  // §38.24: walk the descriptor bit by bit. Each channel is a discrete bit, so
  // a single call closes several channels at once. A bit that cannot be closed
  // is gathered into the error result and reported back to the caller.
  PLI_UINT32 unclosed = 0;
  for (int bit = 0; bit < 32; ++bit) {
    PLI_UINT32 channel = PLI_UINT32{1} << bit;
    if ((mcd & channel) == 0) continue;

    // §38.24: descriptor 1 (the LSB) is predefined for the tool's output
    // channel and current log file; it shall not be closed and so is reported
    // as still open.
    if (bit == 0) {
      unclosed |= channel;
      continue;
    }

    // §38.24: a bit naming no open channel has nothing to close, so it too is
    // reported back rather than silently succeeding.
    if ((mcd_allocated_channels_ & channel) == 0) {
      unclosed |= channel;
      continue;
    }

    // §38.24: close the channel - free it in the shared namespace and drop any
    // file that named it. The namespace is shared with $fopen (§21.3.1), so an
    // fd opened there is closed here the same way.
    mcd_allocated_channels_ &= ~channel;
    for (auto it = mcd_open_files_.begin(); it != mcd_open_files_.end();) {
      if ((it->second & channel) != 0) {
        it->second &= ~channel;
        if (it->second == 0) {
          it = mcd_open_files_.erase(it);
          continue;
        }
      }
      ++it;
    }
  }

  // §38.24: 0 when every requested channel closed, otherwise the mcd of the
  // channels left open.
  return unclosed;
}

PLI_INT32 VpiContext::McdFlush(PLI_UINT32 mcd) {
  // §38.25: a forced flush that cannot complete reports failure and leaves the
  // pending text intact so nothing buffered is lost.
  if (mcd_flush_should_fail_) return 1;

  // §38.25: walk the descriptor bit by bit. Each channel is a discrete bit, so
  // a single mcd can name several files; the buffered output of every named
  // channel is committed in one call. Flushing a channel appends its pending
  // buffer to its committed stream and empties the buffer - the observable
  // effect of forcing the buffered text out to the file.
  for (int bit = 0; bit < 32; ++bit) {
    PLI_UINT32 channel = PLI_UINT32{1} << bit;
    if ((mcd & channel) == 0) continue;
    auto it = mcd_channel_buffers_.find(channel);
    if (it == mcd_channel_buffers_.end()) continue;
    mcd_channel_flushed_[channel].append(it->second);
    it->second.clear();
  }

  // §38.25: every named output buffer was flushed, so report success.
  return 0;
}

PLI_BYTE8* VpiContext::McdName(PLI_UINT32 cd) {
  // §38.26: a descriptor of 0 names no file, so it takes the error return.
  if (cd == 0) return nullptr;

  // §38.26: cd is a single-channel descriptor - one mcd channel, or an fd from
  // $fopen with its MSB set. The file it names is the entry recorded under
  // exactly that descriptor in the shared mcd/fd namespace, the same one
  // vpi_mcd_open() and $fopen populate (§38.27, §21.3.1).
  for (const auto& [name, descriptor] : mcd_open_files_) {
    if (descriptor != cd) continue;
    // §38.26: the name is returned through a buffer reused on every call, so a
    // pointer handed back earlier is overwritten here; a caller that needs to
    // keep the string must copy it. Reserve once so repeated assigns of typical
    // names keep writing into the same allocation, leaving an earlier pointer
    // valid until the next call overwrites its contents.
    if (mcd_name_buffer_.capacity() < 256) mcd_name_buffer_.reserve(256);
    mcd_name_buffer_.assign(name);
    return mcd_name_buffer_.data();
  }

  // §38.26: no open file is named by this descriptor, so report the error.
  return nullptr;
}

PLI_INT32 VpiContext::McdPrintf(PLI_UINT32 mcd, std::string_view text) {
  // §38.28: write the formatted text to one or more channels (up to 31)
  // determined by the descriptor. Each channel is a discrete bit of the integer
  // mcd, so several channels can be written simultaneously in a single call:
  // bit 0 names channel 1 - the tool's output channel and current log file -
  // bit 1 names channel 2, and so on, while the MSB names a file opened as an
  // fd by $fopen (§21.3.1). Every named channel receives the same text,
  // appended to its output buffer (the buffer §38.25 later flushes to the
  // file).
  for (int bit = 0; bit < 32; ++bit) {
    PLI_UINT32 channel = PLI_UINT32{1} << bit;
    if ((mcd & channel) == 0) continue;
    WriteMcdChannel(channel, text);
  }

  // §38.28: the routine returns the number of characters printed. The count is
  // the length of the formatted text, independent of how many channels received
  // it, mirroring C fprintf().
  return static_cast<PLI_INT32>(text.size());
}

PLI_INT32 VpiContext::Printf(std::string_view text) {
  // §38.30: write the formatted text to both the output channel of the tool
  // that invoked the PLI application and the current tool log file. There is no
  // descriptor here, so the destination is fixed: the same text is appended to
  // the tool's output channel buffer and to the log file buffer (the §38.5
  // buffers a later flush commits).
  WriteOutputChannel(text);
  WriteLogFile(text);

  // §38.30: return the number of characters printed - the length of the
  // formatted text - mirroring C printf().
  return static_cast<PLI_INT32>(text.size());
}

// Expand a C printf()-style format string and its variable arguments into a
// std::string, mirroring the measure-then-format idiom used by the VPI printf
// entry points (§38.28/§38.29/§38.30/§38.41). A copy of the incoming va_list is
// used for the sizing pass so the original remains valid for the format pass.
// The caller retains ownership of args: this helper never calls va_end() on it,
// matching the original per-routine behavior (the variadic callers end their
// own list, the v-variant callers leave the caller-owned list untouched).
// Returns false when the format expansion fails (vsnprintf < 0), leaving out
// untouched.
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
  // §38.5: vpi_flush() flushes the output buffers for the simulator's output
  // channel and current log file. Like the other VPI entry points it clears the
  // pending error status (§38.2) before doing its work. Returns 0 on success
  // and nonzero on failure.
  delta::GetGlobalVpiContext().ResetErrorStatus();
  return delta::GetGlobalVpiContext().Flush();
}

PLI_UINT32 vpi_mcd_open(PLI_BYTE8* file) {
  // §38.27: open a file for writing and return its multichannel descriptor.
  // Clears the pending error status (§38.2) like the other entry points. A
  // missing file name names nothing to open, so the routine returns 0 on error.
  delta::GetGlobalVpiContext().ResetErrorStatus();
  if (file == nullptr) return 0;
  return delta::GetGlobalVpiContext().McdOpen(file);
}

PLI_UINT32 vpi_mcd_close(PLI_UINT32 mcd) {
  // §38.24: close the file(s) named by a multichannel descriptor. Clears the
  // pending error status (§38.2) like the other entry points. Returns 0 when
  // every requested channel was closed, otherwise the mcd of the unclosed
  // channels.
  delta::GetGlobalVpiContext().ResetErrorStatus();
  return delta::GetGlobalVpiContext().McdClose(mcd);
}

PLI_INT32 vpi_mcd_flush(PLI_UINT32 mcd) {
  // §38.25: flush the output buffers for the file(s) named by a multichannel
  // descriptor. Clears the pending error status (§38.2) like the other entry
  // points. Returns 0 when the named buffers were flushed, nonzero on failure.
  delta::GetGlobalVpiContext().ResetErrorStatus();
  return delta::GetGlobalVpiContext().McdFlush(mcd);
}

PLI_BYTE8* vpi_mcd_name(PLI_UINT32 cd) {
  // §38.26: return the name of the file represented by a single-channel
  // descriptor. Clears the pending error status (§38.2) like the other entry
  // points. Returns NULL on error, including a descriptor naming no open file.
  delta::GetGlobalVpiContext().ResetErrorStatus();
  return delta::GetGlobalVpiContext().McdName(cd);
}

PLI_INT32 vpi_mcd_printf(PLI_UINT32 mcd, PLI_BYTE8* format, ...) {
  // §38.28: write to the file(s) named by a multichannel descriptor. Clears the
  // pending error status (§38.2) like the other entry points.
  delta::GetGlobalVpiContext().ResetErrorStatus();

  // §38.28: the text is controlled by a format string using the same format as
  // the C fprintf() routine; a missing format string names nothing to print, so
  // the routine reports the error by returning EOF.
  if (format == nullptr) return EOF;

  // §38.28: expand the format string with its variable arguments exactly as
  // C fprintf() would (shared measure-then-format idiom in
  // delta::FormatVaList).
  va_list args;
  va_start(args, format);
  std::string text;
  bool ok = delta::FormatVaList(format, args, text);
  va_end(args);
  if (!ok) {
    // §38.28: the format expansion failed, so report the error with EOF.
    return EOF;
  }

  // §38.28: write the expanded text to every named channel and return the
  // number of characters printed.
  return delta::GetGlobalVpiContext().McdPrintf(mcd, text);
}

PLI_INT32 vpi_mcd_vprintf(PLI_UINT32 mcd, PLI_BYTE8* format, va_list ap) {
  // §38.29: this routine performs the same function as vpi_mcd_printf(), except
  // that the variable-argument list has already been started by the caller. It
  // therefore receives an already-started va_list instead of starting its own.
  // Like the other entry points it clears the pending error status (§38.2).
  delta::GetGlobalVpiContext().ResetErrorStatus();

  // §38.29: the text is controlled by a C fprintf()-style format string; with
  // no format string there is nothing to print, so report the error by
  // returning EOF (matching vpi_mcd_printf()).
  if (format == nullptr) return EOF;

  // §38.29: expand the format with the caller's already-started arguments
  // (shared measure-then-format idiom in delta::FormatVaList, which copies ap
  // for the sizing pass). Ownership of ap stays with the caller, so it is not
  // ended here.
  std::string text;
  if (!delta::FormatVaList(format, ap, text)) {
    // §38.29: the format expansion failed, so report the error with EOF.
    return EOF;
  }

  // §38.29: write the expanded text to every named channel (reusing the §38.28
  // writer) and return the number of characters printed.
  return delta::GetGlobalVpiContext().McdPrintf(mcd, text);
}

PLI_INT32 vpi_printf(PLI_BYTE8* format, ...) {
  // §38.30: write to both the output channel of the tool that invoked the PLI
  // application and the current tool log file. Clears the pending error status
  // (§38.2) like the other entry points.
  delta::GetGlobalVpiContext().ResetErrorStatus();

  // §38.30: the text is controlled by a format string using the same format as
  // the C printf() routine; a missing format string names nothing to print, so
  // the routine reports the error by returning EOF.
  if (format == nullptr) return EOF;

  // §38.30: expand the format string with its variable arguments exactly as
  // C printf() would (shared measure-then-format idiom in delta::FormatVaList).
  va_list args;
  va_start(args, format);
  std::string text;
  bool ok = delta::FormatVaList(format, args, text);
  va_end(args);
  if (!ok) {
    // §38.30: the format expansion failed, so report the error with EOF.
    return EOF;
  }

  // §38.30: write the expanded text to the tool's output channel and log file
  // and return the number of characters printed.
  return delta::GetGlobalVpiContext().Printf(text);
}

PLI_INT32 vpi_vprintf(PLI_BYTE8* format, va_list ap) {
  // §38.41: this routine performs the same function as vpi_printf(), except
  // that the variable-argument list has already been started by the caller. It
  // therefore receives an already-started va_list instead of starting its own.
  // Like the other entry points it clears the pending error status (§38.2).
  delta::GetGlobalVpiContext().ResetErrorStatus();

  // §38.41: the text is controlled by a C printf()-style format string; with no
  // format string there is nothing to print, so report the error by returning
  // EOF (matching vpi_printf()).
  if (format == nullptr) return EOF;

  // §38.41: expand the format with the caller's already-started arguments
  // (shared measure-then-format idiom in delta::FormatVaList, which copies ap
  // for the sizing pass). Ownership of ap stays with the caller, so it is not
  // ended here.
  std::string text;
  if (!delta::FormatVaList(format, ap, text)) {
    // §38.41: the format expansion failed, so report the error with EOF.
    return EOF;
  }

  // §38.41: write the expanded text to the tool's output channel and log file
  // (reusing the §38.30 writer) and return the number of characters written.
  return delta::GetGlobalVpiContext().Printf(text);
}
