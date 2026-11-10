(ns dk.cst.theophrastus.origin
  "Read and build the origins of an entity's values, i.e. where each value
  comes from, in Clojure and ClojureScript.

  An entity read with the :origins option has them in its metadata:

  - :origins maps each property to the origin of its values, or to a map
    of each value to its origin when they differ. A blank node is keyed by
    its symbol.
  - :default-origin, when it's given, is the origin of every value that
    has no entry.

  An origin is the IRI of the named graph that holds a value (or the symbol
  of the blank node that names the graph), :asserted for a graph without a
  name, :inferred when no graph holds the value, or a set of these when
  several graphs hold it.")

(def special-origins
  "The origins that aren't the IRI of a named graph."
  #{:asserted :inferred})

(defn- about
  "The subject of `x`: its :rdf/about when it's a map, or `x` itself."
  [x]
  (if (map? x) (:rdf/about x) x))

(defn- property-values
  "The values of the property value `v`: the elements of a set or vector,
  or `v` itself."
  [v]
  (if (or (set? v) (sequential? v)) v [v]))

(defn origin
  "The origin of the value `v` of the property `p` in `m`, the metadata of
  an entity or another map with its :origins and :default-origin."
  [{:keys [origins default-origin]} p v]
  (let [o (get origins p)]
    (cond
      (map? o)  (get o (about v) default-origin)
      (some? o) o
      :else     default-origin)))

;; a loop that stops at the first value with another origin, since the
;; values of most properties share theirs, and only then a map of them all
(defn- property-origin
  "The entry of the property `p` in :origins, for its values `xs` and the
  function `f` of a property and value to an origin: the origin that every
  value has, a map of each value with an origin to it, or nil when none has
  one. Values of the `default-origin` have none."
  [p xs f default-origin]
  (let [origin-of (fn [x]
                    (let [o (f p x)]
                      (when (not= o default-origin) o)))]
    (loop [s      (seq xs)
           shared ::none]
      (if s
        (let [o (origin-of (about (first s)))]
          (if (or (= ::none shared) (= shared o))
            (recur (next s) o)
            (not-empty (into {}
                             (keep (fn [x]
                                     (let [x (about x)]
                                       (when-some [o (origin-of x)]
                                         [x o]))))
                             xs))))
        (when-not (= ::none shared)
          shared)))))

;; a plain noun for a constructor, as theo/db and rules/reasoner are
(defn origins
  "The :origins of the entity `e`, with the function `f` of a property and
  its value, a blank node as its symbol, to the origin of the value, or nil
  for none. Values of the `default-origin` get no entry either."
  ([e f]
   (origins e f nil))
  ([e f default-origin]
   (persistent!
     (reduce-kv (fn [acc p v]
                  (if (= :rdf/about p)
                    acc
                    (if-some [o (property-origin p (property-values v) f
                                                 default-origin)]
                      (assoc! acc p o)
                      acc)))
                (transient {})
                e))))
