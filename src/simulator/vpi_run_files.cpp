#include "simulator/vpi_run_files.h"

#include <bit>
#include <cstdio>
#include <string>
#include <string_view>

#include "simulator/sim_context.h"
#include "simulator/sim_context_file_tables.h"
#include "simulator/vpi_user.h"

namespace delta {

namespace {

// The file open on the one channel `channel` of the run's table, null for
// none.
FILE* ChannelFile(SimContext& run, PLI_UINT32 channel) {
  return run.FileTables().mcd_channels[std::countr_zero(channel)];
}

}  // namespace

PLI_UINT32 VpiRunMcdOpen(SimContext& run, const std::string& name) {
  // §38.27: a file already open on a channel, through vpi_mcd_open() or the
  // design's $fopen, is handed back on that channel; one opened as an fd is
  // no multichannel descriptor and is opened on a channel of its own.
  for (const auto& [descriptor, opened] : run.FileTables().names) {
    if ((descriptor & SimContext::kFdMsb) == 0 && opened == name) {
      return descriptor;
    }
  }
  return run.OpenMcd(name);
}

PLI_UINT32 VpiRunMcdClose(SimContext& run, PLI_UINT32 mcd) {
  if ((mcd & SimContext::kFdMsb) != 0) {
    // §38.24 with §21.3.1: the standard streams are not closed.
    const bool kOpen =
        mcd != SimContext::kStdinFd && mcd != SimContext::kStdoutFd &&
        mcd != SimContext::kStderrFd && run.GetFileHandle(mcd) != nullptr;
    if (!kOpen) return mcd;
    run.CloseFile(mcd);
    return 0;
  }
  // §38.24: channel 1 is the tool's own and is not closed, and a channel
  // with no file open has nothing to close; both are reported back.
  PLI_UINT32 unclosed = mcd & 1u;
  for (int bit = 1; bit < 31; ++bit) {
    const PLI_UINT32 kChannel = PLI_UINT32{1} << bit;
    if ((mcd & kChannel) == 0) continue;
    if (ChannelFile(run, kChannel) == nullptr) {
      unclosed |= kChannel;
      continue;
    }
    run.CloseFile(kChannel);
  }
  return unclosed;
}

const std::string* VpiRunFileName(SimContext& run, PLI_UINT32 cd) {
  const auto& names = run.FileTables().names;
  auto found = names.find(cd);
  return found == names.end() ? nullptr : &found->second;
}

void VpiRunMcdWrite(SimContext& run, PLI_UINT32 channel,
                    std::string_view text) {
  if (FILE* file = ChannelFile(run, channel)) {
    std::fwrite(text.data(), 1, text.size(), file);
  }
}

bool VpiRunMcdFlush(SimContext& run, PLI_UINT32 channel) {
  FILE* file = ChannelFile(run, channel);
  return file == nullptr || std::fflush(file) == 0;
}

}  // namespace delta
