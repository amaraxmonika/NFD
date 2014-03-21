/* -*- Mode:C++; c-file-style:"gnu"; indent-tabs-mode:nil; -*- */
/**
 * Copyright (C) 2014 Named Data Networking Project
 * See COPYING for copyright and distribution information.
 */

#ifndef NFD_FW_FORWARDER_HPP
#define NFD_FW_FORWARDER_HPP

#include "common.hpp"
#include "core/scheduler.hpp"
#include "forwarder-counter.hpp"
#include "face-table.hpp"
#include "table/fib.hpp"
#include "table/pit.hpp"
#include "table/cs.hpp"
#include "table/measurements.hpp"
#include "table/strategy-choice.hpp"

namespace nfd {

namespace fw {
class Strategy;
} // namespace fw

/** \brief main class of NFD
 *
 *  Forwarder owns all faces and tables, and implements forwarding pipelines.
 */
class Forwarder
{
public:
  Forwarder();

  VIRTUAL_WITH_TESTS
  ~Forwarder();

  const ForwarderCounters&
  getCounters() const;

public: // faces
  FaceTable&
  getFaceTable();

  /** \brief get existing Face
   *
   *  shortcut to .getFaceTable().get(face)
   */
  shared_ptr<Face>
  getFace(FaceId id) const;

  /** \brief add new Face
   *
   *  shortcut to .getFaceTable().add(face)
   */
  void
  addFace(shared_ptr<Face> face);

public: // forwarding entrypoints and tables
  void
  onInterest(Face& face, const Interest& interest);

  void
  onData(Face& face, const Data& data);

  NameTree&
  getNameTree();

  Fib&
  getFib();

  Pit&
  getPit();

  Cs&
  getCs();

  Measurements&
  getMeasurements();

  StrategyChoice&
  getStrategyChoice();

PUBLIC_WITH_TESTS_ELSE_PRIVATE: // pipelines
  /** \brief incoming Interest pipeline
   */
  VIRTUAL_WITH_TESTS void
  onIncomingInterest(Face& inFace, const Interest& interest);

  /** \brief Interest loop pipeline
   */
  VIRTUAL_WITH_TESTS void
  onInterestLoop(Face& inFace, const Interest& interest,
                 shared_ptr<pit::Entry> pitEntry);

  /** \brief outgoing Interest pipeline
   */
  VIRTUAL_WITH_TESTS void
  onOutgoingInterest(shared_ptr<pit::Entry> pitEntry, Face& outFace);

  /** \brief Interest reject pipeline
   */
  VIRTUAL_WITH_TESTS void
  onInterestReject(shared_ptr<pit::Entry> pitEntry);

  /** \brief Interest unsatisfied pipeline
   */
  VIRTUAL_WITH_TESTS void
  onInterestUnsatisfied(shared_ptr<pit::Entry> pitEntry);

  /** \brief incoming Data pipeline
   */
  VIRTUAL_WITH_TESTS void
  onIncomingData(Face& inFace, const Data& data);

  /** \brief Data unsolicited pipeline
   */
  VIRTUAL_WITH_TESTS void
  onDataUnsolicited(Face& inFace, const Data& data);

  /** \brief outgoing Data pipeline
   */
  VIRTUAL_WITH_TESTS void
  onOutgoingData(const Data& data, Face& outFace);

PROTECTED_WITH_TESTS_ELSE_PRIVATE:
  VIRTUAL_WITH_TESTS void
  setUnsatisfyTimer(shared_ptr<pit::Entry> pitEntry);

  VIRTUAL_WITH_TESTS void
  setStragglerTimer(shared_ptr<pit::Entry> pitEntry);

  VIRTUAL_WITH_TESTS void
  cancelUnsatisfyAndStragglerTimer(shared_ptr<pit::Entry> pitEntry);

  /// call trigger (method) on the effective strategy of pitEntry
#ifdef WITH_TESTS
  virtual void
  dispatchToStrategy(shared_ptr<pit::Entry> pitEntry, function<void(fw::Strategy*)> trigger);
#else
  template<class Function>
  void
  dispatchToStrategy(shared_ptr<pit::Entry> pitEntry, Function trigger);
#endif

private:
  ForwarderCounters m_counters;

  FaceTable m_faceTable;

  // tables
  NameTree       m_nameTree;
  Fib            m_fib;
  Pit            m_pit;
  Cs             m_cs;
  Measurements   m_measurements;
  StrategyChoice m_strategyChoice;

  static const Name LOCALHOST_NAME;

  // allow Strategy (base class) to enter pipelines
  friend class fw::Strategy;
};

inline const ForwarderCounters&
Forwarder::getCounters() const
{
  return m_counters;
}

inline FaceTable&
Forwarder::getFaceTable()
{
  return m_faceTable;
}

inline shared_ptr<Face>
Forwarder::getFace(FaceId id) const
{
  return m_faceTable.get(id);
}

inline void
Forwarder::addFace(shared_ptr<Face> face)
{
  m_faceTable.add(face);
}

inline void
Forwarder::onInterest(Face& face, const Interest& interest)
{
  this->onIncomingInterest(face, interest);
}

inline void
Forwarder::onData(Face& face, const Data& data)
{
  this->onIncomingData(face, data);
}

inline NameTree&
Forwarder::getNameTree()
{
  return m_nameTree;
}

inline Fib&
Forwarder::getFib()
{
  return m_fib;
}

inline Pit&
Forwarder::getPit()
{
  return m_pit;
}

inline Cs&
Forwarder::getCs()
{
  return m_cs;
}

inline Measurements&
Forwarder::getMeasurements()
{
  return m_measurements;
}

inline StrategyChoice&
Forwarder::getStrategyChoice()
{
  return m_strategyChoice;
}

#ifdef WITH_TESTS
inline void
Forwarder::dispatchToStrategy(shared_ptr<pit::Entry> pitEntry, function<void(fw::Strategy*)> trigger)
#else
template<class Function>
inline void
Forwarder::dispatchToStrategy(shared_ptr<pit::Entry> pitEntry, Function trigger)
#endif
{
  fw::Strategy& strategy = m_strategyChoice.findEffectiveStrategy(*pitEntry);
  trigger(&strategy);
}

} // namespace nfd

#endif // NFD_FW_FORWARDER_HPP
