#include <cstdint>
#include <cstdio>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "parser/ast_expr.h"
#include "simulator/class_object.h"
#include "simulator/net.h"
#include "simulator/process.h"
#include "simulator/scope.h"
#include "simulator/sim_context.h"
#include "simulator/sim_context_name_tables.h"
#include "simulator/sim_context_types.h"
#include "simulator/sync_objects.h"
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
  // §23.9: "If it is declared locally, then the local item shall be used; if
  // not, the search shall continue upward", and §13.5.1 makes a by-value formal
  // a declaration of the subroutine. A queue declared where a scope is on the
  // stack therefore belongs to that scope and goes away with it, exactly as
  // RegisterArrayInScope puts an array's shape there: registered for the whole
  // run instead, a formal named after a module's queue was the module's queue
  // to every writer in the callee, and still answered to the name after the
  // call returned.
  if (HasLocalScope()) {
    scope_stack_.back().queues[name] = q;
    return q;
  }
  queues_[name] = q;
  return q;
}

// §26.3 with §13.4: the keys a bare name read inside a package subroutine's
// body may stand under, the package's own declaration first and then each
// package an import of it brings the name in from, as PackageScopedKeys
// orders them; none outside any package frame (PackageFrame), and none for a
// hierarchical name, whose head is an instance rather than a declaration of
// the package. FindInPackageScope (sim_context.cpp) reads a variable by them
// and ScopedObjectKeys below puts them ahead of an object's other keys.
std::vector<std::string> SimContext::PackageFrameKeys(
    std::string_view name) const {
  if (name.find('.') != std::string_view::npos) return {};
  const Scope* frame = PackageFrame();
  if (frame == nullptr) return {};
  return PackageScopedKeys(frame->package, name);
}

// §23.9's upward search past the scope frames, for an object held in one of
// the run-long tables rather than in a frame: the keys a bare `name` may
// stand under, in the order the search tries them. A package subroutine's
// body reads the package's own object or an import's first
// (PackageFrameKeys); then, as FindVariable orders them, the generate block
// instances the running process is in, innermost first (GenerateBlockKeys in
// sim_context_name_tables.cpp), the object the running instance declares,
// stored under the instance's prefix (CreateChildModuleVariables in
// lowerer_child.cpp), and the bare key of the enclosing scope, which stays
// the answer for a name that resolved by it before. Without the package keys
// a bare `q.push_back(v)` or `m["k"] = v` inside a package function reached
// no queue and no associative array: the frames held none, no instance's key
// and no bare key matched, and "p1.q", the key the package's object was
// created under (CreatePackageAggregate in lowerer_package_data.cpp), was
// never tried, so the push ran on nothing and `p1::q.size()` afterwards read
// 0. Without the block keys the shape, the elements and the queue an import
// written in a generate block aliases under the block's prefix
// (AliasImportedPackageName in lowerer_import.cpp) were reached by no
// FindArrayInfo or FindQueue of the block's process, §27.3 and §26.3
// notwithstanding: `a[1] = 7` after the block's `import p1::*` set bit 1 of
// the carrier variable FindInGenerateBlock does answer, `foreach (a[i])` ran
// once per bit of it, `$size(a)` answered its width and `q.push_back(2)`
// reached no queue.
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
  // §23.9 searches the innermost scope first, so a queue a subroutine or a
  // begin-end block declares answers its own name while it is on the stack.
  // The key walk below is a separate question and keeps its place under this
  // one: it is what a package's queue reached from inside its subroutine or a
  // module-scoped queue reached from inside an instance is found by, and a
  // formal's copy has to be found before it.
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
  // §23.9 and §13.5.1, as in CreateQueue above.
  if (HasLocalScope()) {
    scope_stack_.back().assoc_arrays[name] = aa;
    return aa;
  }
  assoc_arrays_[name] = aa;
  return aa;
}

AssocArrayObject* SimContext::FindAssocArray(std::string_view name) {
  // §23.9's innermost-first search, as in FindQueue above.
  for (auto frame = scope_stack_.crbegin(); frame != VisibleFramesEnd();
       ++frame) {
    auto local = frame->assoc_arrays.find(name);
    if (local != frame->assoc_arrays.end()) return local->second;
  }
  // §23.9: an associative array declared inside a module instance is stored
  // under that instance's prefix (CreateChildModuleVariables in
  // lowerer_child.cpp), so the prefixed name is what a bare reference from
  // within the instance denotes and is tried ahead of the bare key, a
  // package frame's own keys ahead of both (ScopedObjectKeys above), as in
  // FindQueue. Asked by the bare key alone, no associative array answered the
  // name inside an instance: an element write and read fell to the carrier
  // variable the lowerer creates under the name, and num(), foreach and %p
  // saw none. The bare key stays the answer for an array of the enclosing
  // scope.
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

// §23.9: a net declared inside a module instance is stored under that
// instance's prefix (CreateChildModuleNets in lowerer_child.cpp), so the
// prefixed name is what a bare reference from within the instance denotes and
// is tried first, as in FindQueue above; a net has no scope frame to search
// ahead of it, a subroutine or a block declaring none. Asked by the bare key
// alone, a net declared in an instantiated module was no net to any writer
// naming it from within: a continuous assignment wrote the variable directly
// instead of joining the net's drivers, so a second driver of the same net
// overwrote the first rather than resolving with it, a release re-resolved
// nothing and left the forced value standing (§10.6.2), and %v, $countdrivers
// and a primitive's output found no net -- while a top-level net of the same
// name took every one of them. The unprefixed lookup stays as the answer for a
// net of the enclosing scope.
Net* SimContext::FindNet(std::string_view name) {
  std::string prefix = ActiveInstancePrefix();
  if (!prefix.empty()) {
    auto prefixed = nets_.find(prefix + std::string(name));
    if (prefixed != nets_.end()) return prefixed->second;
  }
  auto it = nets_.find(name);
  return (it != nets_.end()) ? it->second : nullptr;
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

// §23.9: a semaphore declared inside a module instance is stored under that
// instance's prefix (CreateChildModuleVariables in lowerer_child.cpp reaching
// CreateSyncObjectForVar in sync_variable.cpp), so the prefixed name is what a
// bare reference from within the instance denotes and is tried ahead of the
// bare key, a package frame's own keys ahead of both (ScopedObjectKeys
// above), as in FindQueue; a semaphore has no scope frame to search ahead of
// them, a subroutine or a block declaring none. Asked by the bare key alone,
// no semaphore answered the name inside an instance: `s = new(2)` filled no
// bucket, get() and put() ran on none, and try_get() was served by no
// semaphore. The bare key stays the answer for a semaphore of the enclosing
// scope.
SemaphoreObject* SimContext::FindSemaphore(std::string_view name) {
  for (const std::string& key : ScopedObjectKeys(name)) {
    auto it = semaphores_.find(key);
    if (it != semaphores_.end()) return it->second;
  }
  return nullptr;
}

MailboxObject* SimContext::CreateMailbox(std::string_view name, int32_t bound) {
  auto* mb = arena_.Create<MailboxObject>(bound);
  mailboxes_[name] = mb;
  return mb;
}

// §23.9: a mailbox declared inside a module instance is stored under that
// instance's prefix (CreateChildModuleVariables in lowerer_child.cpp reaching
// CreateSyncObjectForVar in sync_variable.cpp), so the keys are walked in the
// order FindSemaphore above walks them (ScopedObjectKeys). The bare key
// stays the answer for a mailbox of the enclosing scope.
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

// §8.23: a class nested in another is held under `Outer::Inner`, the name
// that reaches it from outside the containing class, while a method of the
// containing class names it `Inner` alone, classes being scopes that nest as
// modules do. A name the table does not hold as written is therefore tried
// under the running method's class and then under each class lexically
// containing that one, innermost first, so `Inner i = new` in a method of
// Outer, `Node link` in a method of StringList::Node and `mine = new` on a
// property Outer declares `Inner mine` all construct the nested class.
// §26.7 with Syntax 26-5: `std::` before a built-in class's name reaches the
// same declaration the bare name does, and §26.7 lets no user package be
// called std, so a `std::` head is dropped before the table is asked.
ClassTypeInfo* SimContext::FindClassType(std::string_view name) {
  constexpr std::string_view kStdScope = "std::";
  if (name.substr(0, kStdScope.size()) == kStdScope)
    name = name.substr(kStdScope.size());
  auto it = class_types_.find(name);
  if (it != class_types_.end()) return it->second;
  for (const ClassTypeInfo* scope = CurrentMethodClass(); scope != nullptr;
       scope = scope->enclosing) {
    auto nested =
        class_types_.find(std::string(scope->name) + "::" + std::string(name));
    if (nested != class_types_.end()) return nested->second;
  }
  return nullptr;
}

void SimContext::SetVariableClassType(std::string_view var,
                                      std::string_view type) {
  var_class_types_[var] = type;
}

// §23.9 and §27.4: a class variable a program, an interface or a generate
// block declares is recorded under the name its declaration was lowered as,
// the instance prefix and the generate block prefixes ahead of the declared
// name -- `pr.c` for a program's `c`, `blk[0].c` for a generate block's --
// while a process of that scope names it bare, which FindVariable resolves by
// the process's instance and generate blocks. The record is looked up the
// same way: the name as written, then under each enclosing generate block
// innermost first, then under the instance the name resolves within. Keyed by
// the written name alone, `c.inc()` in the program found no class for `c`
// and ran on no object.
std::string_view SimContext::GetVariableClassType(std::string_view var) const {
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
