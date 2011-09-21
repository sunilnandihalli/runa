(ns immutable-collections.core
  (:use immutable-collections.debug)
  (:require [clojure.inspector :as ins]))

(defn map-keys [mp key-mp]
  (into {} (map (fn [[k v]] [(key-mp k) v]) mp)))

(def max-column-width 40)
(def blank-char \ )
(def coll-seperator \|)
(def row-seperator \-)
(defn center-aligned [s width]
  (let [s-len (count s)
        prefix (quot (- width s-len) 2)
        suffix (- width prefix s-len)]
    (apply str (concat (repeat prefix blank-char)
                       s (repeat suffix blank-char)))))

(defn right-aligned [s width]
  (let [s-len (count s)
        prefix (- width s-len)]
    (apply str (concat (repeat prefix blank-char) s))))
  
(defn indexed-seq [map-or-vec]
  (cond
   (map? map-or-vec) (seq (into (sorted-map) map-or-vec))
   (some #(% map-or-vec) [vector? list?]) (map-indexed vector map-or-vec)))
;; assuming numeric data will not exceed 40 characters...

(defn to-str
  ([cnts width]
     (cond
      (= java.lang.Boolean (class cnts)) (center-aligned (str cnts) width)
      (number? cnts) (right-aligned (str cnts) width)
      :else (str cnts))))
       
(defn print-table
  "Print table of data from vectors/maps"
  ([list-of-column-titles list-of-data-vectors]
     (d (self-keyed-map list-of-column-titles list-of-data-vectors))
     (let [column-width (memoize
                         (fn [coll-id]
                           (min (apply max
                                       (map #(if-let [x (% coll-id)] (count (str x)) 0)
                                            list-of-data-vectors))
                                max-column-width)))
           n-colls (count list-of-column-titles)
           row-seperator-line [(->>
                                (range n-colls)
                                (map (fn [coll-id] (apply str (repeat (column-width coll-id) row-seperator))))
                                (interpose coll-seperator)
                                (apply str))]
           title-line (apply str (interpose coll-seperator (map-indexed #(center-aligned (str %2) (column-width %1)) list-of-column-titles)))
           row-length (memoize
                       (fn [data-vector]
                         (apply max
                                (map (fn [[coll-id contents]]
                                       (let [coll-width (column-width coll-id)
                                             entry-len (count (str contents))]
                                         (+ (quot entry-len coll-width)
                                            (if (zero? (mod entry-len coll-width)) 0 1)))) (indexed-seq data-vector)))))
           print-row (fn [data-vector]
                       (let [row-len (row-length data-vector)]
                         (thrush-with-sym [x]
                           (map (fn [coll-id]
                                  (let [coll-width (column-width coll-id)]
                                    (->> (concat (to-str (data-vector coll-id) coll-width) (repeat blank-char))
                                         (partition coll-width) (map #(apply str %)) (take row-len)))) (range n-colls))
                           (apply map vector x)
                           (map #(interpose coll-seperator %) x)
                           (map #(apply str %) x))))
           all-rows (->>
                     (map print-row list-of-data-vectors)
                     (cons [title-line])
                     (interpose row-seperator-line)
                     (apply concat)
                     (interpose "\n")
                     (apply str))] 
       (println all-rows)))
  ([list-of-data-maps]
     (let [key-to-index (into {} (map-indexed #(do [%2 %1]) (into #{} (mapcat keys list-of-data-maps))))]
       (print-table (sort-by key-to-index (keys key-to-index))
                    (map #(map-keys % key-to-index) list-of-data-maps)))))

#_(print-table [{:a 10 :b "hello" :c "how are you"}
                {:c false :d true :a 34 :b "fsdfsdfsdf" :f "i am fine" :e "yet another really long line .. to see if this will break the code ..." }
                {:a "this is a very long string hopefully it will be longer than forty characters.. let us see how it works "
                 :c 43 :d "how am I"}])