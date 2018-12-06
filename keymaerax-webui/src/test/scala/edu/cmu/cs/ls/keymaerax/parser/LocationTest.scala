package edu.cmu.cs.ls.keymaerax.parser

import edu.cmu.cs.ls.keymaerax.btactics.TacticTestBase

class LocationTest extends TacticTestBase {
  "Regions" should "be advanced correctly by single lines" in {
    Region(1, 1, 10, 10).advanceBy("hello") should be(Region(1, 1, 1, 6), Region(1, 6, 10, 10))
    SuffixRegion(1, 1).advanceBy("hello") should be(Region(1, 1, 1, 6), SuffixRegion(1, 6))
  }

  "Regions" should "be advanced correctly by multiline tokens" in {
    Region(1, 1, 10, 10).advanceBy("hello\nworld") should be(Region(1, 1, 2, 6), Region(2, 6, 10, 10))
    Region(1, 5, 10, 10).advanceBy("hello\n\n\n\n") should be(Region(1, 5, 5, 1), Region(5, 1, 10, 10))
    Region(1, 1, 10, 10).advanceBy("hello\n\nxfactor\n\n") should be(Region(1, 1, 5, 1), Region(5, 1, 10, 10))
    SuffixRegion(1, 2).advanceBy("hello\n\nxfactor\n\n") should be(Region(1, 2, 5, 1), SuffixRegion(5, 1))
  }
}
