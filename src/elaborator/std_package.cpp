#include "elaborator/std_package.h"

#include <optional>
#include <string_view>
#include <vector>

namespace delta {

const std::vector<StdPackageEntry>& StdPackageContents() {
  // §G.1: the semaphore class, the mailbox class, the randomize function, the
  // process class and the weak reference class, in that order.
  // §G.2: each with the subclause its prototype in §G.3 through §G.7 names as
  // defining its semantics.
  static const std::vector<StdPackageEntry> kContents{
      {StdPackageMember::kSemaphore, "semaphore", StdPackageMemberKind::kClass,
       "15.3"},
      {StdPackageMember::kMailbox, "mailbox", StdPackageMemberKind::kClass,
       "15.4"},
      {StdPackageMember::kRandomize, "randomize",
       StdPackageMemberKind::kFunction, "18.12"},
      {StdPackageMember::kProcess, "process", StdPackageMemberKind::kClass,
       "9.7"},
      {StdPackageMember::kWeakReference, "weak_reference",
       StdPackageMemberKind::kClass, "8.30"},
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

std::string_view DefiningSubclauseOfStdPackageMember(StdPackageMember member) {
  for (const StdPackageEntry& entry : StdPackageContents()) {
    if (entry.member == member) return entry.defining_subclause;
  }
  return {};
}

bool StdPackageDefinesSemanticsIn(StdPackageMember member,
                                  std::string_view subclause) {
  // §G.2: the indicated subclause, or one beneath it -- "8.30.1" lies in
  // "8.30" where "8.301" does not.
  const std::string_view kDefining =
      DefiningSubclauseOfStdPackageMember(member);
  if (subclause == kDefining) return true;
  return subclause.size() > kDefining.size() &&
         subclause.substr(0, kDefining.size()) == kDefining &&
         subclause[kDefining.size()] == '.';
}

bool IsStdPackageSystemType(std::string_view name) {
  const std::optional<StdPackageMember> kMember = StdPackageMemberNamed(name);
  return kMember &&
         KindOfStdPackageMember(*kMember) == StdPackageMemberKind::kClass;
}

}  // namespace delta
