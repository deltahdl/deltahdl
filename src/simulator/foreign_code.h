// Annex J: the inclusion of foreign language code into a SystemVerilog
// application. §J.1 has the annex describe common guidelines for that
// inclusion, whose intention is to enable the redistribution of C binaries in
// shared object form. This header states what the annex says; the switches
// and files the guidelines define are what a simulator's driver reads.
#ifndef DELTA_SIMULATOR_FOREIGN_CODE_H_
#define DELTA_SIMULATOR_FOREIGN_CODE_H_

#include <cstdint>

namespace delta {

// §J.1: what the guidelines of the annex are for -- the redistribution of C
// binaries -- and the form they intend it in.
enum class ForeignCodeRedistributionForm : uint8_t {
  kSharedObject,
  kSourceCode,
  kStaticArchiveOnly,
};

ForeignCodeRedistributionForm ForeignCodeIntendedRedistributionForm();

// §J.1: the guidelines are common ones, for the inclusion of foreign language
// code into any SystemVerilog application rather than into one simulator's.
bool ForeignCodeGuidelinesAreCommonToApplications();

}  // namespace delta

#endif  // DELTA_SIMULATOR_FOREIGN_CODE_H_
