// The bodies of the randomization operations
// src/simulator/sim_context_random_stability.h declares: §18.14.3 object
// stability puts an mt19937 on every ClassObject and §18.14.2 thread stability
// puts one on every Process, so each body reads or writes the stream on the
// object or process handed in and nothing SimContext stores. The §18.13.4 and
// §18.13.5 get_randstate/set_randstate pair serializes that stream through
// mt19937's operator<< and operator>>.
//
// The generator SimContext holds, and the draws that choose between it and the
// running process's stream, are in src/simulator/sim_context.h and
// src/simulator/sim_context.cpp.

#include "simulator/sim_context_random_stability.h"

#include <random>
#include <sstream>
#include <string>

#include "simulator/class_object.h"
#include "simulator/process.h"

namespace delta {

std::mt19937& RandomStability::ObjectRng(ClassObject* obj) {
  // §18.14.3 object stability: return the object's own stream so its
  // randomization is independent of every other object and of the context-wide
  // ($random/$urandom) and per-thread generators. Seed lazily the first time
  // the stream is touched, from the value installed at allocation time, so a
  // sequence of draws replays from the same starting state.
  if (!obj->rng_initialized) {
    obj->rng.seed(obj->rng_seed);
    obj->rng_initialized = true;
  }
  return obj->rng;
}

void RandomStability::SeedObjectRng(ClassObject* obj, uint32_t seed) {
  // §18.14.3: srandom() may reseed an object's RNG at any time. Reset both the
  // recorded seed and the live stream so subsequent draws replay the sequence
  // keyed by `seed`, regardless of any draws already taken.
  obj->rng_seed = seed;
  obj->rng.seed(seed);
  obj->rng_initialized = true;
}

std::string RandomStability::GetRandState(ClassObject* obj) {
  // §18.13.4: retrieve the object's current RNG internal state. ObjectRng
  // materializes the stream lazily, so the state reported reflects whatever the
  // object would next draw from. Streaming the generator out captures its full
  // state without consuming any value.
  std::ostringstream os;
  os << ObjectRng(obj);
  return os.str();
}

std::string RandomStability::GetRandState(Process* proc) {
  // §18.13.4: retrieve the current RNG internal state of a process. Mirror the
  // lazy seeding the active-stream path uses so a process that has not yet
  // drawn still reports the state keyed by its installed seed rather than a
  // default generator.
  if (!proc->rng_initialized) {
    proc->rng.seed(proc->rng_seed);
    proc->rng_initialized = true;
  }
  std::ostringstream os;
  os << proc->rng;
  return os.str();
}

void RandomStability::SetRandState(ClassObject* obj, const std::string& state) {
  // §18.13.5: set the object's RNG internal state from `state`. ObjectRng
  // materializes the stream lazily, so touch it first to guarantee the
  // generator exists, then deserialize over it. mt19937's operator>> restores
  // the complete state, so a value produced by GetRandState replays from the
  // exact position it was captured. Mark the stream initialized so a later
  // ObjectRng() does not reseed from the recorded seed and discard the restore.
  std::mt19937& gen = ObjectRng(obj);
  std::istringstream is(state);
  is >> gen;
  obj->rng_initialized = true;
}

void RandomStability::SetRandState(Process* proc, const std::string& state) {
  // §18.13.5: set the process RNG internal state from `state`, mirroring the
  // object path. Ensure the stream is live before deserializing so the restore
  // is not later overwritten by the lazy seed-on-first-use step.
  if (!proc->rng_initialized) {
    proc->rng.seed(proc->rng_seed);
    proc->rng_initialized = true;
  }
  std::istringstream is(state);
  is >> proc->rng;
}

}  // namespace delta
