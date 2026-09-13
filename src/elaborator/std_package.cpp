#include "elaborator/std_package.h"

#include <optional>
#include <string_view>
#include <vector>

namespace delta {

const std::vector<StdPackageEntry>& StdPackageContents() {
  // §G.1: the semaphore class, the mailbox class, the randomize function, the
  // process class and the weak reference class, in that order.
  static const std::vector<StdPackageEntry> kContents{
      {StdPackageMember::kSemaphore, "semaphore", StdPackageMemberKind::kClass},
      {StdPackageMember::kMailbox, "mailbox", StdPackageMemberKind::kClass},
      {StdPackageMember::kRandomize, "randomize",
       StdPackageMemberKind::kFunction},
      {StdPackageMember::kProcess, "process", StdPackageMemberKind::kClass},
      {StdPackageMember::kWeakReference, "weak_reference",
       StdPackageMemberKind::kClass},
  };
  return kContents;
}

std::string_view StdPackageMemberName(StdPackageMember member) {
  for (const StdPackageEntry& entry : StdPackageContents()) {
    if (entry.member == member) return entry.name;
  }
  return {};
}

StdPackageMemberKind KindOfStdPackageMember(StdPackageMember member) {
  for (const StdPackageEntry& entry : StdPackageContents()) {
    if (entry.member == member) return entry.kind;
  }
  return StdPackageMemberKind::kClass;
}

std::optional<StdPackageMember> StdPackageMemberNamed(std::string_view name) {
  for (const StdPackageEntry& entry : StdPackageContents()) {
    if (entry.name == name) return entry.member;
  }
  return std::nullopt;
}

}  // namespace delta
