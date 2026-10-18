#pragma once

#include <cstdint>
#include <vector>

#include "simulator/vpi_user.h"

namespace delta {

// §37.10: what an instance takes from where its definition was written, the
// compiler directives in force there and whether the code is protected, which
// it reports through the properties the figure draws on every instance, and,
// §37.11, where it stands in the instance array it is an element of. Kept
// apart from vpi_object.h, which stands near the size the
// assert-no-oversized-source-files job fails at.
struct VpiInstanceFacts {
  // vpiCellInstance: the definition stands between `celldefine and
  // `endcelldefine (§22.10).
  bool cell = false;
  // vpiProtected: the definition stands in code a decryption envelope
  // contained (§34), whatever the instantiation does.
  bool protected_definition = false;
  // vpiDefNetType: the net type `default_nettype gave the definition's
  // implicit nets (§22.8), vpiNone for `default_nettype none.
  int default_net_type = vpiWire;
  // vpiUnconnDrive: the pull `unconnected_drive gave the definition's
  // unconnected input ports (§22.9), vpiHighZ where none was in force.
  int unconnected_drive = vpiHighZ;
  // vpiDefDelayMode: the delay mode Annex E.4 to E.7's directive selected for
  // the definition, vpiDelayModeNone where none did.
  int delay_mode = vpiDelayModeNone;
  // §37.11 with §38.20: for an element of an instance array, a module's or a
  // primitive's, its index in each of the array's dimensions, leftmost first,
  // which vpi_handle_by_multi_index() names it by; empty for an object of no
  // array.
  std::vector<int64_t> array_indices;
};

}  // namespace delta
