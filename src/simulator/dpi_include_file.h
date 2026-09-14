// Annex I: the svdpi.h include file. §I.1 has the annex list the contents of
// the file -- the constant definitions, structure definitions and routine
// declarations SystemVerilog DPI uses, as the file's own header says -- and
// §I.2 has every SystemVerilog simulator provide the file, its deprecated
// functionality apart. This header states what the annex says of the file;
// the file itself is src/simulator/svdpi.h.
#ifndef DELTA_SIMULATOR_DPI_INCLUDE_FILE_H_
#define DELTA_SIMULATOR_DPI_INCLUDE_FILE_H_

#include <array>
#include <cstdint>
#include <string_view>

namespace delta {

// §I.1: the kinds of content the annex lists for svdpi.h.
enum class DpiSvdpiContent : uint8_t {
  kConstantDefinitions,
  kStructureDefinitions,
  kRoutineDeclarations,
};

// §I.1: the annex that lists the contents of svdpi.h.
std::string_view DpiAnnexListingSvdpiH();

// §I.1: the contents listed, in the order the file's header names them.
std::array<DpiSvdpiContent, 3> DpiSvdpiContents();

// §I.1: whether svdpi.h contains a kind of content: each of the three.
bool DpiSvdpiHContains(DpiSvdpiContent content);

}  // namespace delta

#endif  // DELTA_SIMULATOR_DPI_INCLUDE_FILE_H_
