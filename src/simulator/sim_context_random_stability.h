#pragma once

// The randomization operations SimContext performs on a generator it does not
// hold: §18.14.3 object stability gives every class object its own mt19937 and
// §18.14.2 thread stability gives every process one, so ObjectRng,
// SeedObjectRng and the §18.13.4/§18.13.5 get_randstate/set_randstate pair
// read and write the stream on the ClassObject or the Process handed in and
// touch nothing SimContext stores.
//
// The generator SimContext does hold -- the one seeded from its constructor's
// seed argument, which $random and $urandom draw from when no process is
// running -- stays with the rest of the context in
// src/simulator/sim_context.h, and so do ActiveRng, DrawSeedForChild,
// Random32, Urandom32, SeedUrandom and UrandomRange, each of which chooses
// between that generator and the running process's stream.

#include <cstdint>
#include <random>
#include <string>

#include "simulator/sim_context_types.h"

namespace delta {

class RandomStability {
 public:
  // §18.14.3 object stability: hand back the generator that belongs solely to
  // this instance. Because every object draws from its own stream, the
  // randomization of one instance is independent of any other instance and of
  // the $random/$urandom and per-thread generators. The stream is materialized
  // lazily from the seed installed at allocation (§18.14.1), so the draw
  // sequence stays reproducible.
  std::mt19937& ObjectRng(ClassObject* obj);

  // §18.14.3: an instance can be reseeded at any time via srandom(), letting an
  // object self-seed (typically inside its new method) so its randomization
  // replays under the chosen seed.
  void SeedObjectRng(ClassObject* obj, uint32_t seed);

  // §18.13.4 get_randstate(): hand back the object's current RNG internal state
  // as a string. mt19937 fully serializes its state through operator<<, so the
  // returned value captures the complete generator state -- not merely the
  // seed -- and reading it does not advance the stream. The string's length and
  // contents are implementation dependent.
  std::string GetRandState(ClassObject* obj);

  // §18.13.4 get_randstate(): the same retrieval for the RNG owned by a process
  // (the state obtained via the process's get_randstate() method).
  std::string GetRandState(Process* proc);

  // §18.13.5 set_randstate(): install `state` as the object's RNG internal
  // state, the inverse of GetRandState. mt19937 round-trips its full state
  // through operator>>, so a value previously produced by GetRandState restores
  // the generator to the exact stream position it was read from. The stream is
  // marked live so a later draw does not reseed over the restored state. The
  // value is treated as an opaque string of implementation-dependent length and
  // format; supplying one not obtained from GetRandState is undefined.
  void SetRandState(ClassObject* obj, const std::string& state);

  // §18.13.5 set_randstate(): the same install for the RNG owned by a process
  // (the state given to the process's set_randstate() method).
  void SetRandState(Process* proc, const std::string& state);
};

}  // namespace delta
