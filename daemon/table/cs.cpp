/* -*- Mode:C++; c-file-style:"gnu"; indent-tabs-mode:nil; -*- */
/**
 * Copyright (c) 2014,  Regents of the University of California,
 *                      Arizona Board of Regents,
 *                      Colorado State University,
 *                      University Pierre & Marie Curie, Sorbonne University,
 *                      Washington University in St. Louis,
 *                      Beijing Institute of Technology,
 *                      The University of Memphis
 *
 * This file is part of NFD (Named Data Networking Forwarding Daemon).
 * See AUTHORS.md for complete list of NFD authors and contributors.
 *
 * NFD is free software: you can redistribute it and/or modify it under the terms
 * of the GNU General Public License as published by the Free Software Foundation,
 * either version 3 of the License, or (at your option) any later version.
 *
 * NFD is distributed in the hope that it will be useful, but WITHOUT ANY WARRANTY;
 * without even the implied warranty of MERCHANTABILITY or FITNESS FOR A PARTICULAR
 * PURPOSE.  See the GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License along with
 * NFD, e.g., in COPYING.md file.  If not, see <http://www.gnu.org/licenses/>.
 *
 * \author Ilya Moiseenko <http://ilyamoiseenko.com/>
 * \author Junxiao Shi <http://www.cs.arizona.edu/people/shijunxiao/>
 * \author Alexander Afanasyev <http://lasr.cs.ucla.edu/afanasyev/index.html>
 */

#include "cs.hpp"
#include "core/logger.hpp"
#include "core/random.hpp"

#include <ndn-cxx/util/crypto.hpp>
#include <ndn-cxx/security/signature-sha256-with-rsa.hpp>

#include <boost/random/bernoulli_distribution.hpp>

/// max skip list layers
static const size_t SKIPLIST_MAX_LAYERS = 32;
/// probability for an entry in layer N to appear also in layer N+1
static const double SKIPLIST_PROBABILITY = 0.25;

NFD_LOG_INIT("ContentStore");

namespace nfd {

Cs::Cs(size_t nMaxPackets)
  : m_nMaxPackets(nMaxPackets)
  , m_nPackets(0)
{
  // adding new data structures
  for (size_t i = 0; i < m_nMaxPackets; i++){
    CSPool.push(new cs::Entry());
  }

}

Cs::~Cs()
{
  // evict all items from CS
  while (evictItem())
    ;

  // adding for new data structure
  // all remaining items not evicted from table
  while (!CSPool.empty())
  {
    delete CSPool.front();
    CSPool.pop();

  }
}

size_t
Cs::size() const
{
  return m_nPackets; // size of the first layer in a skip list
}

void
Cs::setLimit(size_t nMaxPackets)
{
  size_t oldNMaxPackets = m_nMaxPackets;
  m_nMaxPackets = nMaxPackets;

  // remove items from content store
  while (size() > m_nMaxPackets) {
    evictItem();
  }

  // add/remove items from memory pool
  if (m_nMaxPackets >= oldNMaxPackets) {
    for (size_t i = oldNMaxPackets; i < m_nMaxPackets; i++) {
      CSPool.push(new cs::Entry()); // chase: new
    }
  }
  else {
    for (size_t i = oldNMaxPackets; i > m_nMaxPackets; i--) {

      // chase: new
      delete CSPool.front();
      CSPool.pop();
    }
  }
}

size_t
Cs::getLimit() const
{
  return m_nMaxPackets;
}

bool
Cs::insert(const Data& data, bool isUnsolicited)
{
  NFD_LOG_TRACE("insert() " << data.getFullName());

  if (isFull())
    {
      evictItem();
    }

  // adding new data structures
  cs::Entry* temp = insertQueue(data, isUnsolicited); // add to csqueue
  insertTable(temp, isUnsolicited); // add to csmap
  m_nPackets++;
  return true;

}

bool
Cs::isFull() const
{
  if (size() >= m_nMaxPackets) //size of the first layer vs. max size
    return true;

  return false;
}

bool
Cs::evictItem()
{
  //NFD_LOG_TRACE("evictItem()");

  // added by chase for new hash map
  // Implementing simple eviction policy where
  // we only remove the first element in the queue
  if (!CSQueue.empty())
  {
    // get first item in queue
    cs::Entry* entry = CSQueue.front();
    std::string key = entry->getName().toUri();

    // remove entry from CSMap
    CSMap.erase(key);

    // release all references to entry
    // and add entry back to memory pool
    entry->release();
    CSPool.push(entry);

   
    m_nPackets--;
    return true;

  }
  
  return false;
}

const Data*
Cs::find(const Interest& interest) const
{
  NFD_LOG_TRACE("find() " << interest.getName());
  //NFD_LOG_TRACE("find().getUri() " << interest.getName().toUri());
  boost::unordered_map<std::string,cs::Entry*>::const_iterator it;
  //std::map<std::string,cs::Entry*>::const_iterator it;
  //std::map<Name,cs::Entry*>::const_iterator it;
  it = CSMap.find(interest.getName().toUri());
  if(it!=CSMap.end())
  {
      //NFD_LOG_TRACE("find():and(it->second... " << it->second->getName());
      return &(it->second->getData());
  }
  else
      return 0;

}

bool
Cs::doesComplyWithSelectors(const Interest& interest,
                            cs::Entry* entry,
                            bool doesInterestContainDigest) const
{
  NFD_LOG_TRACE("doesComplyWithSelectors()");

  /// \todo The following detection is not correct
  ///       1. If Interest name ends with 32-octet component doesn't mean that this component is
  ///          digest
  ///       2. Only min/max selectors (both 0) can be specified, all other selectors do not
  ///          make sense for interests with digest (though not sure if we need to enforce this)

  if (doesInterestContainDigest)
    {
      if (interest.getName().get(-1) != entry->getFullName().get(-1))
        {
          NFD_LOG_TRACE("violates implicit digest");
          return false;
        }
    }

  if (!doesInterestContainDigest)
    {
      if (interest.getMinSuffixComponents() >= 0)
        {
          size_t minDataNameLength = interest.getName().size() + interest.getMinSuffixComponents();

          bool isSatisfied = (minDataNameLength <= entry->getFullName().size());
          if (!isSatisfied)
            {
              NFD_LOG_TRACE("violates minComponents");
              return false;
            }
        }

      if (interest.getMaxSuffixComponents() >= 0)
        {
          size_t maxDataNameLength = interest.getName().size() + interest.getMaxSuffixComponents();

          bool isSatisfied = (maxDataNameLength >= entry->getFullName().size());
          if (!isSatisfied)
            {
              NFD_LOG_TRACE("violates maxComponents");
              return false;
            }
        }
    }

  if (interest.getMustBeFresh() && entry->getStaleTime() < time::steady_clock::now())
    {
      NFD_LOG_TRACE("violates mustBeFresh");
      return false;
    }

  if (!interest.getPublisherPublicKeyLocator().empty())
    {
      if (entry->getData().getSignature().getType() == ndn::Signature::Sha256WithRsa)
        {
          ndn::SignatureSha256WithRsa rsaSignature(entry->getData().getSignature());
          if (rsaSignature.getKeyLocator() != interest.getPublisherPublicKeyLocator())
            {
              NFD_LOG_TRACE("violates publisher key selector");
              return false;
            }
        }
      else
        {
          NFD_LOG_TRACE("violates publisher key selector");
          return false;
        }
    }

  if (doesInterestContainDigest)
    {
      const ndn::name::Component& lastComponent = entry->getFullName().get(-1);

      if (!lastComponent.empty())
        {
          if (interest.getExclude().isExcluded(lastComponent))
            {
              NFD_LOG_TRACE("violates exclusion");
              return false;
            }
        }
    }
  else
    {
      if (entry->getFullName().size() >= interest.getName().size() + 1)
        {
          const ndn::name::Component& nextComponent = entry->getFullName()
                                                        .get(interest.getName().size());
          if (!nextComponent.empty())
            {
              if (interest.getExclude().isExcluded(nextComponent))
                {
                  NFD_LOG_TRACE("violates exclusion");
                  return false;
                }
            }
        }
    }

  NFD_LOG_TRACE("complies");
  return true;
}

bool
Cs::recognizeInterestWithDigest(const Interest& interest, cs::Entry* entry) const
{
  // only when min selector is not specified or specified with value of 0
  // and Interest's name length is exactly the length of the name of CS entry
  if (interest.getMinSuffixComponents() <= 0 &&
      interest.getName().size() == (entry->getFullName().size()))
    {
      const ndn::name::Component& last = interest.getName().get(-1);
      if (last.value_size() == ndn::crypto::SHA256_DIGEST_SIZE)
        {
          NFD_LOG_TRACE("digest recognized");
          return true;
        }
    }

  return false;
}

void
Cs::erase(const Name& exactName)
{
  NFD_LOG_TRACE("erase() " << exactName << ", "
                << "skipList size " << size());

  // added by chase for new data structure
  // Get Entity
  boost::unordered_map<std::string,cs::Entry*>::iterator it;
  it=CSMap.find(exactName.toUri());
  CSMap.erase (it); 
  it->second->release(); 
  CSPool.push(it->second);
  m_nPackets--;
  return;
}

// adding new methods for data structure
//bool
//Cs::insertTable(const Data& data, bool isUnsolicited)
//{
//  return false;
// adding this for git
//}
// better 
bool
Cs::insertTable(cs::Entry* entry, bool isUnsolicited){

  NFD_LOG_TRACE("insertTable() " << entry->getName().toUri() );
  // First we need to retrieve the char* name of entry for
  // hash function
  std::string key = entry->getName().toUri();
  //Name key = entry->getName();

  // Using the uri of entry we add it to the hash map
  CSMap[key] = entry;
  
  return true; // need to change
}

// not currently used
bool
Cs::eraseFromTable(cs::Entry* entry)
{

  // need to add something that will deal with collisions
  //entry->release();
  //m_freeCsEntries.push(entry);
  //m_nPackets--;

  // access iterator
  boost::unordered_map<std::string,cs::Entry*>::iterator it;
  it=CSMap.find(entry->getName().toUri());
  CSMap.erase (it); 

  return true;

}

cs::Entry*
Cs::insertQueue(const Data& data, bool isUnsolicited)
{
  // get memory from pool
  cs::Entry* entry = CSPool.front();
  CSPool.pop();
  //m_nPackets++; // increment number of packets in map
  
  // set contents of new entry
  entry->setData(data, isUnsolicited);

  // finally add new entry to end of queue
  // if entry unsolicited, add to front of queue 
  // to be evicted first
  if (isUnsolicited)
    CSQueue.push_front(entry);
  else
    CSQueue.push_back(entry);

  return entry;
}

// Not currently used
cs::Entry*
Cs::eraseFromQueue(){

  // Pop the first element in the queue
  cs::Entry* entry = CSQueue.front();

  // release all references to it
  // and add it back to memory pool
  entry->release();
  CSPool.push(entry);
  
  return entry;
}


} //namespace nfd
