#include <algorithm>
#include <sstream>

#include "common/diagnostic.h"
#include "simulator/coverage.h"
#include "simulator/net.h"
#include "simulator/process.h"
#include "simulator/sim_context.h"
#include "simulator/vcd_writer.h"

namespace delta {

void QueueObject::AssignFreshIds() {
  element_ids.resize(elements.size());
  for (auto& id : element_ids) id = AllocateId();
}

QueueObject* SimContext::CreateQueue(std::string_view name, uint32_t elem_width,
                                     int32_t max_size, bool is_4state) {
  auto* q = arena_.Create<QueueObject>();
  q->elem_width = elem_width;
  q->is_4state = is_4state;
  q->max_size = max_size;
  queues_[name] = q;
  return q;
}

QueueObject* SimContext::FindQueue(std::string_view name) {
  auto it = queues_.find(name);
  return (it != queues_.end()) ? it->second : nullptr;
}

uint32_t AssocArrayObject::Size() const {
  return static_cast<uint32_t>(is_string_key ? str_data.size()
                                             : int_data.size());
}

namespace {

// Populates a freshly created AssocArrayObject's fields from the
// CreateAssocArray arguments (§7.8: element shape + index type).
void PopulateAssocArrayFields(AssocArrayObject* aa, uint32_t elem_width,
                              bool is_string_key, const AssocArraySpec& spec) {
  aa->elem_width = elem_width;
  aa->is_string_key = is_string_key;
  aa->is_wildcard = spec.is_wildcard;
  aa->index_width = spec.index_width;
  aa->is_4state = spec.is_4state;
  aa->is_index_signed = spec.is_index_signed;
}

}  // namespace

AssocArrayObject* SimContext::CreateAssocArray(std::string_view name,
                                               uint32_t elem_width,
                                               bool is_string_key,
                                               const AssocArraySpec& spec) {
  auto* aa = arena_.Create<AssocArrayObject>();
  PopulateAssocArrayFields(aa, elem_width, is_string_key, spec);
  assoc_arrays_[name] = aa;
  return aa;
}

AssocArrayObject* SimContext::FindAssocArray(std::string_view name) {
  auto it = assoc_arrays_.find(name);
  return (it != assoc_arrays_.end()) ? it->second : nullptr;
}

void SimContext::SetVariableTag(std::string_view var_name,
                                std::string_view tag) {
  var_tags_[var_name] = std::string(tag);
}

std::string_view SimContext::GetVariableTag(std::string_view var_name) const {
  auto it = var_tags_.find(var_name);
  if (it == var_tags_.end()) return {};
  return it->second;
}

void SimContext::EnsureStdioDescriptors() {
  if (stdio_descriptors_ready_) return;
  stdio_descriptors_ready_ = true;
  // STDIN/STDOUT/STDERR are pre-opened by §21.3.1 at the reserved fd values.
  // Channel 0 of an mcd points at the standard output (§21.3.1, LSB rule).
  file_descriptors_[kStdinFd] = stdin;
  file_descriptors_[kStdoutFd] = stdout;
  file_descriptors_[kStderrFd] = stderr;
  mcd_channels_[0] = stdout;
}

uint32_t SimContext::OpenFile(std::string_view filename,
                              std::string_view mode) {
  EnsureStdioDescriptors();
  std::string fname(filename);
  std::string fmode(mode);
  FILE* fp = std::fopen(fname.c_str(), fmode.c_str());
  if (!fp) return 0;
  // Lowest free slot in 3..0x7FFFFFFF, so $fopen reuses channels closed earlier
  // (§21.3.1).
  uint32_t slot = 3;
  while (file_descriptors_.count(kFdMsb | slot) != 0) ++slot;
  uint32_t fd = kFdMsb | slot;
  file_descriptors_[fd] = fp;
  // §21.3.4: only the "r"/"r+" type families authorize reading. Every such
  // type string begins with 'r', so track readability by that leading letter.
  if (!fmode.empty() && fmode.front() == 'r') readable_fds_.insert(fd);
  return fd;
}

uint32_t SimContext::OpenMcd(std::string_view filename) {
  EnsureStdioDescriptors();
  // mcd LSB (bit 0) is reserved for stdout; MSB (bit 31) must remain clear.
  // §21.3.1 limits an implementation to channels 1..30 for output files.
  for (uint32_t bit = 1; bit < 31; ++bit) {
    if (mcd_channels_[bit] == nullptr) {
      std::string fname(filename);
      FILE* fp = std::fopen(fname.c_str(), "w");
      if (!fp) return 0;
      mcd_channels_[bit] = fp;
      return uint32_t{1} << bit;
    }
  }
  return 0;
}

void SimContext::CloseFile(uint32_t descriptor) {
  EnsureStdioDescriptors();
  if ((descriptor & kFdMsb) != 0) {
    // STDIN/STDOUT/STDERR are not closable per §21.3.1.
    if (descriptor == kStdinFd || descriptor == kStdoutFd ||
        descriptor == kStderrFd) {
      return;
    }
    auto it = file_descriptors_.find(descriptor);
    if (it == file_descriptors_.end()) return;
    std::fclose(it->second);
    file_descriptors_.erase(it);
    readable_fds_.erase(descriptor);
    fileio_errors_.erase(descriptor);
    fd_eof_detected_.erase(descriptor);
    return;
  }
  // Multichannel descriptor: every bit set selects a channel to close.
  for (uint32_t bit = 1; bit < 31; ++bit) {
    if ((descriptor & (uint32_t{1} << bit)) == 0) continue;
    if (mcd_channels_[bit] == nullptr) continue;
    std::fclose(mcd_channels_[bit]);
    mcd_channels_[bit] = nullptr;
  }
}

FILE* SimContext::GetFileHandle(uint32_t fd) {
  EnsureStdioDescriptors();
  auto it = file_descriptors_.find(fd);
  return (it != file_descriptors_.end()) ? it->second : nullptr;
}

void SimContext::SetFileIoError(uint32_t fd, int32_t code, std::string msg) {
  fileio_errors_[fd] = FileIoError{code, std::move(msg)};
}

void SimContext::ClearFileIoError(uint32_t fd) { fileio_errors_.erase(fd); }

const SimContext::FileIoError* SimContext::GetFileIoError(uint32_t fd) const {
  auto it = fileio_errors_.find(fd);
  return (it != fileio_errors_.end()) ? &it->second : nullptr;
}

void SimContext::SetFdEofDetected(uint32_t fd, bool detected) {
  if (detected) {
    fd_eof_detected_.insert(fd);
  } else {
    fd_eof_detected_.erase(fd);
  }
}

bool SimContext::FdEofDetected(uint32_t fd) const {
  return fd_eof_detected_.count(fd) != 0;
}

bool SimContext::IsFdReadable(uint32_t fd) const {
  // §21.3.4: STDIN is pre-opened for reading; STDOUT/STDERR are append-only.
  if (fd == kStdinFd) return true;
  if (fd == kStdoutFd || fd == kStderrFd) return false;
  return readable_fds_.count(fd) != 0;
}

std::vector<FILE*> SimContext::GetMcdFiles(uint32_t mcd) {
  EnsureStdioDescriptors();
  std::vector<FILE*> result;
  for (uint32_t bit = 0; bit < 31; ++bit) {
    if ((mcd & (uint32_t{1} << bit)) == 0) continue;
    if (mcd_channels_[bit] != nullptr) result.push_back(mcd_channels_[bit]);
  }
  return result;
}

SemaphoreObject* SimContext::CreateSemaphore(std::string_view name,
                                             int32_t keys) {
  auto* sem = arena_.Create<SemaphoreObject>(keys);
  semaphores_[name] = sem;
  return sem;
}

SemaphoreObject* SimContext::FindSemaphore(std::string_view name) {
  auto it = semaphores_.find(name);
  return (it != semaphores_.end()) ? it->second : nullptr;
}

MailboxObject* SimContext::CreateMailbox(std::string_view name, int32_t bound) {
  auto* mb = arena_.Create<MailboxObject>(bound);
  mailboxes_[name] = mb;
  return mb;
}

MailboxObject* SimContext::FindMailbox(std::string_view name) {
  auto it = mailboxes_.find(name);
  return (it != mailboxes_.end()) ? it->second : nullptr;
}

void SimContext::SetEventTriggered(std::string_view name) {
  event_triggered_[name] = scheduler_.CurrentTime().ticks;

  auto* var = FindVariable(name);
  if (var) var->triggered_ticks = scheduler_.CurrentTime().ticks;
}

bool SimContext::IsEventTriggered(std::string_view name) const {
  auto vit = variables_.find(name);
  if (vit != variables_.end())
    return vit->second->triggered_ticks == scheduler_.CurrentTime().ticks;
  auto it = event_triggered_.find(name);
  if (it == event_triggered_.end()) return false;
  return it->second == scheduler_.CurrentTime().ticks;
}

void SimContext::RegisterClassType(std::string_view name, ClassTypeInfo* info) {
  class_types_[name] = info;
}

ClassTypeInfo* SimContext::FindClassType(std::string_view name) {
  auto it = class_types_.find(name);
  return (it != class_types_.end()) ? it->second : nullptr;
}

void SimContext::SetVariableClassType(std::string_view var,
                                      std::string_view type) {
  var_class_types_[var] = type;
}

std::string_view SimContext::GetVariableClassType(std::string_view var) const {
  auto it = var_class_types_.find(var);
  return (it != var_class_types_.end()) ? it->second : std::string_view{};
}

void SimContext::SetVariableClassParamExprs(std::string_view var,
                                            std::vector<Expr*> exprs) {
  var_class_param_exprs_[var] = std::move(exprs);
}

static const std::vector<Expr*> kEmptyExprVec;

const std::vector<Expr*>& SimContext::GetVariableClassParamExprs(
    std::string_view var) const {
  auto it = var_class_param_exprs_.find(var);
  return (it != var_class_param_exprs_.end()) ? it->second : kEmptyExprVec;
}

}  // namespace delta
