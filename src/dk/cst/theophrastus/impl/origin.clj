(ns dk.cst.theophrastus.impl.origin
  "The origins that entity and pull record in the metadata of their maps,
  from the graphs of a db that hold each triple."
  (:require [dk.cst.theophrastus.convert :as convert]
            [dk.cst.theophrastus.impl.entity :as entity]
            [dk.cst.theophrastus.origin :as origin]
            [dk.cst.theophrastus.term :as term])
  (:import [java.util Collection HashMap HashSet Iterator LinkedHashMap List
            Map Set]
           [org.apache.jena.graph Graph Node NodeFactory Triple]
           [org.apache.jena.query Dataset]
           [org.apache.jena.reasoner BaseInfGraph]
           [org.apache.jena.sparql.core DatasetGraph GraphView Quad]))

(defn origin-selection
  "The origins that the :origins option `x` selects, with `prefixes` for
  IRIs: the IRIs of the :graphs (or :all) and the :special origins."
  [x prefixes]
  (let [canonical (fn [o]
                    (or (origin/special-origins o)
                        (term/iri o prefixes)
                        (throw (ex-info (str "Not an origin: " (pr-str o))
                                        {:origin o}))))]
    (cond
      (true? x) {:graphs :all :special origin/special-origins}
      (set? x)  (let [cs (map canonical x)]
                  {:graphs  (into #{} (remove keyword?) cs)
                   :special (into #{} (filter keyword?) cs)})
      :else     (throw (ex-info (str "Not an :origins option: " (pr-str x))
                                {:origins x})))))

(defn origin-namer
  "A function of an origin, a graph Node or a keyword, to the name that the
  `selection` records it under, or nil when it isn't selected, with
  `prefixes` for IRIs. A set of graphs selects them by IRI, so a graph named
  by a blank node is only selected along with all the others."
  [{:keys [graphs special]} prefixes]
  (let [cache (HashMap.)]
    (fn [o]
      (if (keyword? o)
        (special o)
        (if (.containsKey cache o)
          (.get cache o)
          (let [n (when (or (= :all graphs)
                            (and (.isURI ^Node o)
                                 (contains? graphs (.getURI ^Node o))))
                    (convert/data o prefixes))]
            (.put cache o n)
            n))))))

(defn default-name
  "The :default-origin `x` as the origins are named, with `prefixes` for
  IRIs, so that it compares with the names recorded."
  [x prefixes]
  (if-let [iri (when-not (origin/special-origins x)
                 (term/iri x prefixes))]
    (convert/data (NodeFactory/createURI ^String iri) prefixes)
    x))

(defn graph-scope
  "The named graphs that the Graph `g` is a view of, as its :dsg and its
  :graphs (:all, or a set of graph Nodes), or nil for a graph without a
  name."
  [^Graph g]
  (when (instance? GraphView g)
    (let [n (.getGraphName ^GraphView g)]
      (when-not (or (nil? n) (Quad/isDefaultGraph n))
        {:dsg    (.getDataset ^GraphView g)
         :graphs (if (Quad/isUnionGraph n) :all #{n})}))))

(defn origin-sources
  "Where the triples are that `db` reads with its Graph `g`: in its :named
  graphs (see graph-scope), read as the :named-graph, in its :unnamed
  Graphs, and, when `g` :infers?, nowhere."
  [{:keys [^Dataset dataset default-graph]} ^Graph g]
  (cond
    (instance? BaseInfGraph g)
    (let [raw    (.getRawGraph ^BaseInfGraph g)
          schema (.getSchemaGraph ^BaseInfGraph g)
          scope  (graph-scope raw)]
      {:named       scope
       :named-graph raw
       :unnamed     (cond-> []
                      (nil? scope)   (conj raw)
                      (some? schema) (conj schema))
       :infers?     true})

    (and dataset (set? default-graph))
    {:named {:dsg    (.asDatasetGraph dataset)
             :graphs (into #{} (map #(NodeFactory/createURI ^String %))
                           default-graph)}}

    :else
    (if-let [scope (graph-scope g)]
      {:named scope}
      {:unnamed [g]})))

(defn constant-origin
  "The origin of every triple from the `sources`, named by `name-of`, when
  they hold just one graph and infer nothing, or ::varies."
  [{:keys [named unnamed infers?]} name-of]
  (let [graphs (:graphs named)]
    (cond
      infers?                                  ::varies
      (and (nil? named) (= 1 (count unnamed))) (name-of :asserted)
      (and (set? graphs) (= 1 (count graphs))) (name-of (first graphs))
      :else                                    ::varies)))

(defn find-set
  "The triples of the Graph `g` that match s p o."
  ^Set [^Graph g ^Node s ^Node p ^Node o]
  (HashSet. ^Collection (.toList (.find g s p o))))

(defn add-quads!
  "Add each of the `quads` to the map `m` of a triple to the graph Node
  that holds it, or to a set of the Nodes when several do."
  [^Map m ^Iterator quads]
  (while (.hasNext quads)
    (let [^Quad q (.next quads)
          t       (.asTriple q)
          g       (.getGraph q)
          held    (.get m t)]
      (.put m t (cond
                  (nil? held) g
                  (set? held) (conj held g)
                  :else       #{held g})))))

(defn named-triples
  "A map of each triple that matches s p o in the named graphs of a scope
  (see graph-scope) to the graph Node that holds it, or a set of the Nodes
  when several do, in the order found. Only the `wanted` graphs are read:
  :all, or a set of graph IRIs."
  ^Map [{:keys [^DatasetGraph dsg graphs]} wanted ^Node s ^Node p ^Node o]
  (let [m (LinkedHashMap.)]
    ;; one find of the quads in all of them, or one find per graph
    (if (and (= :all graphs) (= :all wanted))
      (add-quads! m (.findNG dsg Node/ANY s p o))
      (doseq [^Node n (cond
                        (= :all wanted) graphs
                        (= :all graphs) (map #(NodeFactory/createURI ^String %)
                                             wanted)
                        :else           (filter #(and (.isURI ^Node %)
                                                      (contains?
                                                        wanted
                                                        (.getURI ^Node %)))
                                                graphs))]
        (add-quads! m (.find dsg n s p o))))
    m))

(defn held-name
  "The name of the origin of a triple that `held`, a graph Node or a set of
  them, holds, as `name-of` gives it, or nil."
  [name-of held]
  (if (set? held)
    (entity/property-value (keep name-of held))
    (some-> held name-of)))

(defn triple-origin
  "A function of a triple that matches s p o to the name of its origin, as
  `name-of` gives it for the `selection`, from the `sources`. The graphs
  are read once, for all the triples that match."
  [{:keys [named named-graph unnamed infers?]} {:keys [graphs special]}
   name-of ^Node s ^Node p ^Node o]
  (let [asserted? (contains? special :asserted)
        inferred? (and infers? (contains? special :inferred))
        by-graph  (when (and named (or (= :all graphs) (seq graphs)))
                    (named-triples named graphs s p o))
        unnamed   (when (or asserted? inferred?)
                    (mapv #(find-set % s p o) unnamed))
        ;; the triples of every named graph, to tell an inferred triple
        ;; from one in a graph that isn't selected
        in-named  (when (and inferred? named)
                    (if (= :all graphs)
                      (.keySet ^Map by-graph)
                      (find-set named-graph s p o)))]
    (fn [t]
      (let [held     (when by-graph (.get ^Map by-graph t))
            unnamed? (some #(.contains ^Set % t) unnamed)]
        (cond
          ;; the usual case: one named graph holds the triple
          (and (instance? Node held) (not (and asserted? unnamed?)))
          (name-of held)

          (nil? held)
          (if unnamed?
            (when asserted?
              (name-of :asserted))
            (when (and inferred?
                       (not (and in-named (.contains ^Set in-named t))))
              (name-of :inferred)))

          :else
          (entity/property-value
            (cond-> (into #{} (keep name-of)
                          (if (set? held) held (some-> held list)))
              (and asserted? unnamed?) (conj (name-of :asserted)))))))))

(defn origin-recording
  "How to record the origins of the values that `db` reads with its Graph
  `g`, as the `opts` of entity ask for them, or nil when they ask for none:
  a function of a find pattern s p o to a function of each triple that
  matches it to its origin, unless every triple has the same :constant
  origin, the :default-origin, and the named graphs whose :quads to read
  instead of triples. With :blank-node-origins?, the maps of blank nodes get
  their origins too."
  ;; a boolean option ends in ?, as :transactional? of db does
  [{:keys [prefixes] :as db} g
   {:keys [origins default-origin blank-node-origins?]}]
  (when (or origins (some? default-origin) blank-node-origins?)
    ;; a value of an origin that isn't recorded would read as the default
    (when (and (some? default-origin) (set? origins))
      (throw (ex-info (str "A :default-origin needs all the origins, not a "
                           "set of :origins")
                      {:origins origins :default-origin default-origin})))
    (let [selection (origin-selection (or origins true) prefixes)
          name-of   (origin-namer selection prefixes)
          sources   (origin-sources db g)
          constant  (constant-origin sources name-of)]
      {:name-of             name-of
       :origin-of           (fn [s p o]
                              (triple-origin sources selection name-of s p o))
       :constant            constant
       :default-origin      (some-> default-origin
                                    (default-name prefixes))
       :blank-node-origins? blank-node-origins?
       ;; without inference, the quads of a subject are its triples and
       ;; their graphs in one read
       :quads               (when (and (= ::varies constant)
                                       (not (:infers? sources)))
                              (:named sources))})))

(defn origins-meta
  "The metadata of the entity `e` with the origins of its values, as the
  `recording` has them, from the Jena `triples` of its subject Node `s` and
  their [p o] `pairs`. The function `origin-of-triple` gives the origin of
  each triple when the triples were read with their graphs."
  [{:keys [origin-of constant default-origin]} e ^Node s ^List triples pairs
   origin-of-triple]
  (let [origins (cond
                  (= ::varies constant)
                  (let [origin-of-triple (or origin-of-triple
                                             (origin-of s Node/ANY Node/ANY))
                        by-property      (HashMap.)]
                    (dotimes [i (.size triples)]
                      (when-some [o (origin-of-triple (.get triples i))]
                        (let [[p x]   (nth pairs i)
                              ^Map xs (or (.get by-property p)
                                          (let [xs (HashMap.)]
                                            (.put by-property p xs)
                                            xs))]
                          (.put xs x o))))
                    (origin/origins e
                                    (fn [p x]
                                      (when-some [^Map xs (.get by-property p)]
                                        (.get xs x)))
                                    default-origin))

                  ;; every value has the one origin, or none is recorded
                  (or (nil? constant) (= constant default-origin))
                  {}

                  :else
                  (into {}
                        (keep (fn [k] (when-not (= :rdf/about k) [k constant])))
                        (keys e)))]
    (cond-> {:origins origins}
      (some? default-origin) (assoc :default-origin default-origin))))

(defn link-origins
  "The origins of the `links`, a map of a reverse predicate to the subjects
  that link to `subject` by it, as the `recording` has them. The triples
  of each link are in `read`, by predicate and subject."
  [{:keys [origin-of constant default-origin]} ^Map read links subject
   prefixes]
  (let [s       (convert/node subject prefixes)
        by-link (when (= ::varies constant)
                  (into {}
                        (for [rp (keys links)
                              :let [p         (convert/reverse-property rp)
                                    origin-of (origin-of
                                                Node/ANY
                                                (convert/node p prefixes)
                                                s)]]
                          [rp (into {}
                                    (keep (fn [^Triple t]
                                            (when-some [o (origin-of t)]
                                              [(convert/data (.getSubject t)
                                                             prefixes)
                                               o])))
                                    (.get read [p subject]))])))]
    (origin/origins links
                    (if by-link
                      (fn [rp x] (get-in by-link [rp x]))
                      (constantly constant))
                    default-origin)))
