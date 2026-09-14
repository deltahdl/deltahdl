// Annex K: the vpi_user.h include file. §K.1 has the annex show the contents
// of the file, and has the file be a normative include file that every
// SystemVerilog simulator shall provide. This header states what the annex
// says of the file; the file itself is src/simulator/vpi_user.h.
#ifndef DELTA_SIMULATOR_VPI_INCLUDE_FILE_H_
#define DELTA_SIMULATOR_VPI_INCLUDE_FILE_H_

#include <string_view>

namespace delta {

// §K.1: the annex that shows the contents of vpi_user.h.
std::string_view VpiAnnexShowingVpiUserH();

// §K.1: the file whose contents the annex shows.
std::string_view VpiUserHFileName();

// §K.1: vpi_user.h is a normative include file, not an informative one.
bool VpiUserHIsNormative();

// §K.1: every SystemVerilog simulator shall provide vpi_user.h.
bool VpiUserHIsProvidedByEverySimulator();

}  // namespace delta

#endif  // DELTA_SIMULATOR_VPI_INCLUDE_FILE_H_
