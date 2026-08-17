#pragma once

#include <string_view>

namespace delta {

// §6.16: whether one of the string methods writes the string it is called on.
// Six of the eighteen do -- §6.16.2's putc replaces a character, and §6.16.11
// through §6.16.15's itoa, hextoa, octtoa, bintoa and realtoa each store a
// converted number into the string -- and the rest answer a value and leave
// their object alone. Eighteen counts methods rather than subclauses, of which
// §6.16 has fifteen: §6.16.9 defines atoi, atohex, atooct and atobin together.
//
// The question has two askers, which is why it is not answered inside either.
// The simulator dispatches these six to the helpers that perform the write, and
// the elaborator refuses the call where the object is a constant, since §6.20
// rules that "constants are named data objects that never change". A list
// written out in both places would drift, and the way it would drift is a
// method added to one and not the other, which is silence rather than a
// mismatch: the elaborator would let the call through and the simulator would
// carry out the write.
inline bool StringMethodWritesItsObject(std::string_view method) {
  return method == "putc" || method == "itoa" || method == "hextoa" ||
         method == "octtoa" || method == "bintoa" || method == "realtoa";
}

}  // namespace delta
