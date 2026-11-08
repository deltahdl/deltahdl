#pragma once

#include <cstdint>
#include <functional>
#include <string>
#include <string_view>

namespace delta {

inline constexpr std::string_view kDecryptLicenseKeyword = "decrypt_license";
inline constexpr std::string_view kRuntimeLicenseKeyword = "runtime_license";

inline constexpr std::string_view kLibrarySubkeyword = "library";
inline constexpr std::string_view kEntrySubkeyword = "entry";
inline constexpr std::string_view kFeatureSubkeyword = "feature";
inline constexpr std::string_view kExitSubkeyword = "exit";
inline constexpr std::string_view kMatchSubkeyword = "match";

struct ProtectLicense {
  std::string library;
  std::string entry;
  std::string feature;
  std::string exit;
  bool has_exit = false;
  uint64_t match = 0;
  bool has_match = false;
  bool stated = false;
};

ProtectLicense ParseProtectLicense(std::string_view value);

struct ProtectLicenseAnswer {
  bool called = false;
  int64_t returned = 0;
  std::string why_not_called;
};

using ProtectLicenseAsk =
    std::function<ProtectLicenseAnswer(const ProtectLicense&)>;

bool ProtectLicenseGranted(const ProtectLicense& license,
                           const ProtectLicenseAnswer& answer);

std::string ProtectLicenseRefusal(std::string_view keyword,
                                  const ProtectLicense& license,
                                  const ProtectLicenseAnswer& answer);

}  // namespace delta
