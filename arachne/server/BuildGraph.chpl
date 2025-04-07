module BuildGraph {
  // Chapel modules.
  use ParallelIO;

  // Arkouda modules.
  use AryUtil;

  record edge { var u, v: int(64); }
  record weightedEdge { var u, v, w: int(64); }

  /* Deserializer to parse lines of type "1 2" with any amount of whitespace between. */
  proc ref edge.deserialize(reader, ref deserializer) throws {
    reader.read(this.u);
    reader.readLiteral(b" ");
    reader.read(this.v);
  }

  /* Deserializer to parse lines of type "1 2 3" with any amount of whitespace between. */
  proc ref weightedEdge.deserialize(reader, ref deserializer) throws {
    reader.read(this.u);
    reader.readLiteral(b" ");
    reader.read(this.v);
    reader.readLiteral(b" ");
    reader.read(this.w);
  }

  /* Creates block-distributed arrays for src, dst, and maybe wgt from a given .tsv file. */
  proc readTSVFileDistributed(path, weighted) throws {
    if !weighted {
      var edges = readDelimitedAsBlockArray(path, t=edge);
      var src = makeDistArray(edges.size, int);
      var dst = makeDistArray(edges.size, int);
      var wgt = makeDistArray(0, int);

      forall (e,i) in zip(edges,edges.domain) {
        src[i] = e.u;
        dst[i] = e.v;
      }
      return (src,dst,wgt);
    } else {
      var edges = readDelimitedAsBlockArray(path, t=weightedEdge);
      var src = makeDistArray(edges.size, int);
      var dst = makeDistArray(edges.size, int);
      var wgt = makeDistArray(edges.size, int);

      forall (e,i) in zip(edges,edges.domain) {
        src[i] = e.u;
        dst[i] = e.v;
        wgt[i] = e.w;
      }
      return (src,dst,wgt);
    }
  }

  /* Creates local rectangular arrays for src, dst, and maybe wgt from a given .tsv file. */
  proc readTSVFileLocal(path, weighted) throws {
    if !weighted {
      var edges = readDelimitedAsArray(path, t=edge);
      var src: [0..<edges.size] int;
      var dst: [0..<edges.size] int;
      var wgt: [0..0] int;

      forall (e,i) in zip(edges,edges.domain) {
        src[i] = e.u;
        dst[i] = e.v;
      }
      return (src,dst,wgt);
    } else {
      var edges = readDelimitedAsArray(path, t=weightedEdge);
      var src: [0..<edges.size] int;
      var dst: [0..<edges.size] int;
      var wgt: [0..<edges.size] int;

      forall (e,i) in zip(edges,edges.domain) {
        src[i] = e.u;
        dst[i] = e.v;
        wgt[i] = e.w;
      }
      return (src,dst,wgt);
    }
  }
}