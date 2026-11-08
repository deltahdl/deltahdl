#include <algorithm>
#include <cerrno>
#include <charconv>
#include <cstddef>
#include <cstdint>
#include <cstdio>
#include <cstring>
#include <string>
#include <string_view>
#include <system_error>
#include <tuple>
#include <unordered_map>
#include <utility>
#include <vector>

#include "common/arena.h"
#include "parser/ast_expr.h"
#include "simulator/class_object.h"
#include "simulator/net.h"
#include "simulator/process.h"
#include "simulator/scope.h"
#include "simulator/sim_context.h"
#include "simulator/sim_context_file_tables.h"
#include "simulator/sim_context_name_tables.h"
#include "simulator/sim_context_types.h"
#include "simulator/sync_objects.h"
#include "simulator/unit_scopes.h"
#include "simulator/vcd_writer.h"

namespace delta {

void QueueObject::AssignFreshIds() {
  element_ids.resize(elements.size());
  for (auto& id : element_ids) id = AllocateId();
}

void QueueObject::AllocateIdsForAppended() {
  while (element_ids.size() < elements.size())
    element_ids.push_back(AllocateId());
}

QueueObject* SimContext::CreateQueue(std::string_view name, uint32_t elem_width,
                                     int32_t max_size, bool is_4state) {
  auto* q = arena_.Create<QueueObject>();
  q->elem_width = elem_width;
  q->is_4state = is_4state;
  q->max_size = max_size;
  if (HasLocalScope()) {
    scope_stack_.back().queues[name] = q;
    return q;
  }
  queues_[name] = q;
  return q;
}

std::vector<std::string> SimContext::PackageFrameKeys(
    std::string_view name) const {
  if (name.find('.') != std::string_view::npos) return {};
  const Scope* frame = PackageFrame();
  if (frame == nullptr) return {};
  return PackageScopedKeys(frame->package, name);
}

bool SimContext::IsUnitPathFromRoot(std::string_view name) {
  std::size_t dot = name.find('.');
  if (dot == std::string_view::npos) return false;
  const Scope* frame = PackageFrame();
  if (frame == nullptr || !UnitScopes::IsUnitScope(frame->package))
    return false;
  std::string_view head = name.substr(0, dot);
  return FindLocalVariable(head) == nullptr &&
         FindInPackageScope(head) == nullptr;
}

Variable* SimContext::FindUnitPathVariable(std::string_view name) {
  if (!IsUnitPathFromRoot(name)) return nullptr;
  auto it = variables_.find(RootedStorageKey(name));
  return it != variables_.end() ? it->second : nullptr;
}

std::vector<std::string> SimContext::ScopedObjectKeys(
    std::string_view name) const {
  std::vector<std::string> keys = PackageFrameKeys(name);
  std::string prefix = ActiveInstancePrefix();
  if (current_process_ != nullptr) {
    for (std::string& key :
         GenerateBlockKeys(prefix, current_process_->gen_prefixes, name)) {
      keys.push_back(std::move(key));
    }
  }
  if (!prefix.empty()) keys.push_back(prefix + std::string(name));
  keys.emplace_back(name);
  return keys;
}

QueueObject* SimContext::FindQueue(std::string_view name) {
  for (auto frame = scope_stack_.crbegin(); frame != VisibleFramesEnd();
       ++frame) {
    auto local = frame->queues.find(name);
    if (local != frame->queues.end()) return local->second;
  }
  for (const std::string& key : ScopedObjectKeys(name)) {
    auto it = queues_.find(key);
    if (it != queues_.end()) return it->second;
  }
  return nullptr;
}

uint32_t AssocArrayObject::Size() const {
  return static_cast<uint32_t>(is_string_key ? str_data.size()
                                             : int_data.size());
}

namespace {

void PopulateAssocArrayFields(AssocArrayObject* aa, uint32_t elem_width,
                              bool is_string_key, const AssocArraySpec& spec) {
  aa->elem_width = elem_width;
  aa->is_string_key = is_string_key;
  aa->is_wildcard = spec.is_wildcard;
  aa->index_width = spec.index_width;
  aa->is_4state = spec.is_4state;
  aa->is_index_signed = spec.is_index_signed;
  aa->index_class = spec.index_class;
  aa->index_type_name = spec.index_type_name;
}

}  // namespace

AssocArrayObject* SimContext::CreateAssocArray(std::string_view name,
                                               uint32_t elem_width,
                                               bool is_string_key,
                                               const AssocArraySpec& spec) {
  auto* aa = arena_.Create<AssocArrayObject>();
  PopulateAssocArrayFields(aa, elem_width, is_string_key, spec);
  if (HasLocalScope()) {
    scope_stack_.back().assoc_arrays[name] = aa;
    return aa;
  }
  assoc_arrays_[name] = aa;
  return aa;
}

AssocArrayObject* SimContext::FindAssocArray(std::string_view name) {
  for (auto frame = scope_stack_.crbegin(); frame != VisibleFramesEnd();
       ++frame) {
    auto local = frame->assoc_arrays.find(name);
    if (local != frame->assoc_arrays.end()) return local->second;
  }
  for (const std::string& key : ScopedObjectKeys(name)) {
    auto it = assoc_arrays_.find(key);
    if (it != assoc_arrays_.end()) return it->second;
  }
  return nullptr;
}

void SimContext::AliasQueue(std::string_view alias_name,
                            std::string_view target_name) {
  auto it = queues_.find(target_name);
  if (it != queues_.end()) queues_[alias_name] = it->second;
}

void SimContext::AliasAssocArray(std::string_view alias_name,
                                 std::string_view target_name) {
  auto it = assoc_arrays_.find(target_name);
  if (it != assoc_arrays_.end()) assoc_arrays_[alias_name] = it->second;
}

void SimContext::AliasSemaphore(std::string_view alias_name,
                                std::string_view target_name) {
  auto it = semaphores_.find(target_name);
  if (it != semaphores_.end()) semaphores_[alias_name] = it->second;
}

void SimContext::AliasMailbox(std::string_view alias_name,
                              std::string_view target_name) {
  auto it = mailboxes_.find(target_name);
  if (it != mailboxes_.end()) mailboxes_[alias_name] = it->second;
}

static Net* FindNetInGenerateBlock(
    const std::unordered_map<std::string_view, Net*>& nets, const Process* proc,
    const std::string& prefix, std::string_view name) {
  if (proc == nullptr) return nullptr;
  for (const std::string& key :
       GenerateBlockKeys(prefix, proc->gen_prefixes, name)) {
    auto found = nets.find(key);
    if (found != nets.end()) return found->second;
  }
  return nullptr;
}

Net* SimContext::FindNet(std::string_view name) {
  constexpr std::string_view kRootPrefix = "$root.";
  if (name.starts_with(kRootPrefix)) {
    auto it = nets_.find(RootedStorageKey(name.substr(kRootPrefix.size())));
    return (it != nets_.end()) ? it->second : nullptr;
  }
  std::string prefix = ActiveInstancePrefix();
  if (Net* in_block =
          FindNetInGenerateBlock(nets_, current_process_, prefix, name)) {
    return in_block;
  }
  if (!prefix.empty()) {
    auto prefixed = nets_.find(prefix + std::string(name));
    if (prefixed != nets_.end()) return prefixed->second;
  }
  if (Net* outer = FindInNestedDeclOuterScopes(nets_, prefix, name))
    return outer;
  if (!prefix.empty() && name.find('.') == std::string_view::npos &&
      !IsImportedName(name)) {
    return nullptr;
  }
  auto it = nets_.find(name);
  return (it != nets_.end()) ? it->second : nullptr;
}

static ClassObject* PropertyTagOwner(std::string_view key,
                                     const SimContext& ctx,
                                     std::string_view& path) {
  if (key.empty() || key.front() != '@') return nullptr;
  size_t dot = key.find('.');
  if (dot == std::string_view::npos) return nullptr;
  uint64_t handle = 0;
  auto [end, ec] = std::from_chars(key.data() + 1, key.data() + dot, handle);
  if (ec != std::errc() || end != key.data() + dot) return nullptr;
  path = key.substr(dot + 1);
  return ctx.GetClassObject(handle);
}

void SimContext::SetVariableTag(std::string_view var_name,
                                std::string_view tag) {
  std::string_view path;
  if (ClassObject* obj = PropertyTagOwner(var_name, *this, path)) {
    obj->property_tags[std::string(path)] = std::string(tag);
    return;
  }
  var_tags_[var_name] = std::string(tag);
}

std::string_view SimContext::GetVariableTag(std::string_view var_name) const {
  std::string_view path;
  if (const ClassObject* obj = PropertyTagOwner(var_name, *this, path)) {
    auto it = obj->property_tags.find(std::string(path));
    if (it == obj->property_tags.end()) return {};
    return it->second;
  }
  auto it = var_tags_.find(var_name);
  if (it == var_tags_.end()) return {};
  return it->second;
}

void SimContext::EnsureStdioDescriptors() {
  if (files_.stdio_ready) return;
  files_.stdio_ready = true;
  files_.descriptors[kStdinFd] = stdin;
  files_.descriptors[kStdoutFd] = stdout;
  files_.descriptors[kStderrFd] = stderr;
  files_.mcd_channels[0] = stdout;
}

static void RecordFailedOpen(SimContext& ctx) {
  int code = errno != 0 ? errno : ENOENT;
  ctx.SetFileIoError(0, code, std::strerror(code));
}

uint32_t SimContext::OpenFile(std::string_view filename,
                              std::string_view mode) {
  EnsureStdioDescriptors();
  std::string fname(filename);
  std::string fmode(mode);
  FILE* fp = std::fopen(fname.c_str(), fmode.c_str());
  if (!fp) {
    RecordFailedOpen(*this);
    return 0;
  }
  uint32_t slot = 3;
  while (files_.descriptors.count(kFdMsb | slot) != 0) ++slot;
  uint32_t fd = kFdMsb | slot;
  files_.descriptors[fd] = fp;
  files_.names[fd] = fname;
  if (!fmode.empty() && fmode.front() == 'r') files_.readable.insert(fd);
  return fd;
}

uint32_t SimContext::OpenMcd(std::string_view filename) {
  EnsureStdioDescriptors();
  for (uint32_t bit = 1; bit < 31; ++bit) {
    if (files_.mcd_channels[bit] == nullptr) {
      std::string fname(filename);
      FILE* fp = std::fopen(fname.c_str(), "w");
      if (!fp) {
        RecordFailedOpen(*this);
        return 0;
      }
      files_.mcd_channels[bit] = fp;
      files_.names[uint32_t{1} << bit] = fname;
      return uint32_t{1} << bit;
    }
  }
  return 0;
}

static bool WritesThroughClosed(uint32_t writer, uint32_t closed) {
  if ((closed & SimContext::kFdMsb) != 0) return writer == closed;
  return (writer & SimContext::kFdMsb) == 0 && (writer & closed & ~1U) != 0;
}

void SimContext::CloseFile(uint32_t descriptor) {
  EnsureStdioDescriptors();
  bool is_fd = (descriptor & kFdMsb) != 0;
  for (auto& monitor : files_.monitors) {
    if (WritesThroughClosed(monitor->descriptor, descriptor)) {
      monitor->cancelled = true;
    }
  }
  if (is_fd) {
    if (descriptor == kStdinFd || descriptor == kStdoutFd ||
        descriptor == kStderrFd) {
      return;
    }
    auto it = files_.descriptors.find(descriptor);
    if (it == files_.descriptors.end()) return;
    std::fclose(it->second);
    files_.descriptors.erase(it);
    files_.readable.erase(descriptor);
    files_.errors.erase(descriptor);
    files_.eof_detected.erase(descriptor);
    files_.pushback.erase(descriptor);
    files_.names.erase(descriptor);
    return;
  }
  for (uint32_t bit = 1; bit < 31; ++bit) {
    if ((descriptor & (uint32_t{1} << bit)) == 0) continue;
    if (files_.mcd_channels[bit] == nullptr) continue;
    std::fclose(files_.mcd_channels[bit]);
    files_.mcd_channels[bit] = nullptr;
    files_.names.erase(uint32_t{1} << bit);
  }
}

FILE* SimContext::GetFileHandle(uint32_t fd) {
  EnsureStdioDescriptors();
  auto it = files_.descriptors.find(fd);
  return (it != files_.descriptors.end()) ? it->second : nullptr;
}

void SimContext::SetFileIoError(uint32_t fd, int32_t code, std::string msg) {
  files_.errors[fd] = FileIoError{code, std::move(msg)};
}

void SimContext::ClearFileIoError(uint32_t fd) { files_.errors.erase(fd); }

const FileIoError* SimContext::GetFileIoError(uint32_t fd) const {
  auto it = files_.errors.find(fd);
  return (it != files_.errors.end()) ? &it->second : nullptr;
}

void SimContext::SetFdEofDetected(uint32_t fd, bool detected) {
  if (detected) {
    files_.eof_detected.insert(fd);
  } else {
    files_.eof_detected.erase(fd);
  }
}

bool SimContext::FdEofDetected(uint32_t fd) const {
  return files_.eof_detected.count(fd) != 0;
}

bool SimContext::IsFdReadable(uint32_t fd) const {
  if (fd == kStdinFd) return true;
  if (fd == kStdoutFd || fd == kStderrFd) return false;
  return files_.readable.count(fd) != 0;
}

std::vector<FILE*> SimContext::GetMcdFiles(uint32_t mcd) {
  EnsureStdioDescriptors();
  std::vector<FILE*> result;
  for (uint32_t bit = 0; bit < 31; ++bit) {
    if ((mcd & (uint32_t{1} << bit)) == 0) continue;
    if (files_.mcd_channels[bit] != nullptr)
      result.push_back(files_.mcd_channels[bit]);
  }
  return result;
}

SemaphoreObject* SimContext::CreateSemaphore(std::string_view name,
                                             int32_t keys) {
  auto* sem = arena_.Create<SemaphoreObject>(keys);
  semaphores_[name] = sem;
  RecordContainedSemaphore(sem);
  return sem;
}

SemaphoreObject* SimContext::FindSemaphore(std::string_view name) {
  for (const std::string& key : ScopedObjectKeys(name)) {
    auto it = semaphores_.find(key);
    if (it != semaphores_.end()) return it->second;
  }
  return nullptr;
}

SemaphoreObject** SimContext::SemaphoreSlot(std::string_view name) {
  for (const std::string& key : ScopedObjectKeys(name)) {
    auto it = semaphores_.find(key);
    if (it != semaphores_.end()) return &it->second;
  }
  return nullptr;
}

MailboxObject** SimContext::MailboxSlot(std::string_view name) {
  for (const std::string& key : ScopedObjectKeys(name)) {
    auto it = mailboxes_.find(key);
    if (it != mailboxes_.end()) return &it->second;
  }
  return nullptr;
}

MailboxObject* SimContext::CreateMailbox(std::string_view name, int32_t bound) {
  auto* mb = arena_.Create<MailboxObject>(bound);
  mailboxes_[name] = mb;
  RecordContainedMailbox(mb);
  return mb;
}

MailboxObject* SimContext::FindMailbox(std::string_view name) {
  for (const std::string& key : ScopedObjectKeys(name)) {
    auto it = mailboxes_.find(key);
    if (it != mailboxes_.end()) return it->second;
  }
  return nullptr;
}

void SimContext::SetEventTriggered(std::string_view name) {
  event_triggered_[name] = scheduler_.CurrentTime().ticks;

  auto* var = FindVariable(name);
  if (var) var->triggered_ticks = scheduler_.CurrentTime().ticks;
}

bool SimContext::IsEventTriggered(std::string_view name) const {
  std::string local = ActiveInstancePrefix() + std::string(name);
  for (std::string_view key : {std::string_view(local), name}) {
    auto vit = variables_.find(key);
    if (vit != variables_.end())
      return vit->second->triggered_ticks == scheduler_.CurrentTime().ticks;
  }
  auto it = event_triggered_.find(name);
  if (it == event_triggered_.end()) return false;
  return it->second == scheduler_.CurrentTime().ticks;
}

static ClassTypeInfo* ClassUnder(
    const std::unordered_map<std::string_view, ClassTypeInfo*>& table,
    std::string_view scope, std::string_view name) {
  const auto kFound = table.find(std::string(scope) + "::" + std::string(name));
  return kFound == table.end() ? nullptr : kFound->second;
}

static ClassTypeInfo* NestedClassOf(
    const std::unordered_map<std::string_view, ClassTypeInfo*>& table,
    const ClassTypeInfo& base, std::string_view name) {
  std::string key = std::string(base.name) + "::" + std::string(name);
  if (!base.instance_scope.empty()) {
    key = std::string(base.instance_scope) + "::" + key;
  }
  const auto kFound = table.find(key);
  return kFound == table.end() ? nullptr : kFound->second;
}

void SimContext::RegisterClassType(std::string_view name, ClassTypeInfo* info) {
  if (class_scope_.empty()) {
    class_types_[name] = info;
    return;
  }
  class_types_[*arena_.Create<std::string>(class_scope_ +
                                           "::" + std::string(name))] = info;
}

std::string SimContext::SetClassInstanceScope(std::string scope) {
  if (!scope.empty()) instance_classes_ = true;
  std::swap(scope, class_scope_);
  return scope;
}

static bool DropStdScope(std::string_view& name) {
  constexpr std::string_view kStdScope = "std::";
  if (!name.starts_with(kStdScope)) return true;
  name.remove_prefix(kStdScope.size());
  return name != "semaphore" && name != "mailbox";
}

static ClassTypeInfo* NestedClassInScopes(
    const std::unordered_map<std::string_view, ClassTypeInfo*>& table,
    const ClassTypeInfo* method_class, std::string_view name) {
  for (const ClassTypeInfo* scope = method_class; scope != nullptr;
       scope = scope->enclosing) {
    for (const ClassTypeInfo* base = scope; base != nullptr;
         base = base->parent) {
      if (ClassTypeInfo* nested = NestedClassOf(table, *base, name)) {
        return nested;
      }
    }
  }
  return nullptr;
}

ClassTypeInfo* SimContext::ExactClassType(std::string_view name) {
  return ClassUnder(class_types_, class_scope_, name);
}

ClassTypeInfo* SimContext::FindClassType(std::string_view name) const {
  if (!DropStdScope(name)) return nullptr;
  ClassTypeInfo* own = units_.Separate()
                           ? ClassUnder(class_types_, ActiveUnitScope(), name)
                           : nullptr;
  if (own == nullptr && instance_classes_) {
    own = ClassUnder(class_types_, ActiveInstancePrefix(), name);
  }
  if (own != nullptr) return own;
  auto it = class_types_.find(name);
  if (it != class_types_.end() && it->second != nullptr) return it->second;
  if (ClassTypeInfo* nested =
          NestedClassInScopes(class_types_, CurrentMethodClass(), name)) {
    return nested;
  }
  const Scope* frame = PackageFrame();
  return frame != nullptr ? ClassUnder(class_types_, frame->package, name)
                          : nullptr;
}

std::vector<ClassTypeInfo*> SimContext::RegisteredClassTypes(bool all) const {
  std::vector<ClassTypeInfo*> classes;
  for (const auto& [key, info] : class_types_) {
    if (info != nullptr && (all || key == info->name)) classes.push_back(info);
  }
  if (!all) return classes;
  std::ranges::sort(classes);
  classes.erase(std::ranges::unique(classes).begin(), classes.end());
  std::ranges::stable_sort(
      classes, [](const ClassTypeInfo* a, const ClassTypeInfo* b) {
        return std::tie(a->instance_scope, a->package, a->name) <
               std::tie(b->instance_scope, b->package, b->name);
      });
  return classes;
}

void SimContext::SetVariableClassType(std::string_view var,
                                      std::string_view type) {
  RecordLocalClassType(var, type);
  var_class_types_[var] = type;
}

std::string_view SimContext::GetVariableClassType(std::string_view var) const {
  if (const std::string_view* local = FindLocalClassType(var)) return *local;
  auto it = var_class_types_.find(var);
  if (it != var_class_types_.end()) return it->second;
  std::string prefix = ActiveInstancePrefix();
  if (current_process_ != nullptr) {
    const std::vector<std::string>& blocks = current_process_->gen_prefixes;
    for (auto block = blocks.rbegin(); block != blocks.rend(); ++block) {
      auto found = var_class_types_.find(prefix + *block + std::string(var));
      if (found != var_class_types_.end()) return found->second;
    }
  }
  if (prefix.empty()) return {};
  auto found = var_class_types_.find(prefix + std::string(var));
  return (found != var_class_types_.end()) ? found->second : std::string_view{};
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
