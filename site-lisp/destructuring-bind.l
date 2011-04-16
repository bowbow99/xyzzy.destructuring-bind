;;; -*- mode: lisp; package: destructuring-bind -*-
;;;
;;; destructuring-bind.l --- Common Lisp ‚Ì destructuring-bind
;;;
;;; Author:     bowbow99  <bowbow99@gmail.com>
;;; Version:    0.00.00
;;; Category:
;;; License:    MIT (see COPYING.mit)
;;; Commentary: (see README.md)
;;; ChangeLog:  (see ChangeLog)

;;; Code:


(in-package :lisp)

(export '(destructuring-bind
          &allow-other-keys
          ))

(defconstant &allow-other-keys '&allow-other-keys)

(defpackage :destructuring-bind
  (:use :lisp))

(in-package :destructuring-bind)

(defparameter *destructuring-lambda-list-keywords*
  (list &optional &rest &key &aux &body &whole &environment &allow-other-keys))

(defmacro with-ca/dr ((car-var cdr-var) cons &body body)
  `(let ((#1=#:cons ,cons))
     (let ((,car-var (car #1#))
           (,cdr-var (cdr #1#)))
       ,@body)))
#+xyzzy
(setf (get 'with-ca/dr 'ed:lisp-indent-hook) 2)

(defmacro with-places ((&rest places) object &body body)
  `(let ((#1=#:object ,object))
     (let (,@(mapcar (lambda (place)
                       `(,place (,place #1#)))
               places))
       ,@body)))
#+xyzzy
(setf (get 'with-places 'ed:lisp-indent-hook) 2)




(defun %assert-list-length (list min max)
  (declare (type list list)
           (type (or integer (eql nil)) min max))
  "Check LIST is a list with expected number of elements, and return the LIST as-is."
  (unless (listp list)
    (error 'type-error :datum list :expected-type 'list))
  (let ((len (list-length list)))
    (unless (or (null min) (<= min len))
      (error 'too-few-arguments :datum list))
    (unless (or (null max) (<= len max))
      (error 'too-many-arguments :datum list))
    list))


(defparameter *state/parser-alist*
  '((&required . parse-&required)
    (&optional . parse-&optional)
    ;(&rest     . parse-&rest)
    (&key      . parse-&key)
    ))

(defparameter *lambda-list* nil)

(defun parse-lambda-list (lambda-list form)
  (declare (type list lambda-list))
  (multiple-value-bind (whole-var lambda-list)
      (if (eql (car lambda-list) '&whole)
        (values (second lambda-list) (cddr lambda-list))
        (values (gensym "whole-")    lambda-list))
    (let ((vars  (list whole-var))
          (forms (list))
          (tail  whole-var)
          (state '&required)
          (rest-var nil)
          (min-length 0)
          (max-length 0))
      (progn
        (do ((lambda-list lambda-list (cdr lambda-list)))
            ((null lambda-list))
          (if (symbolp lambda-list)
            ; lambda-list was a dotted-list
            (setq lambda-list (list nil '&rest lambda-list))
            (with-ca/dr (x rest) lambda-list
              (if (member x *destructuring-lambda-list-keywords*)
                (case x
                  ((&optional)
                   (setq state x))
                  ((&rest &body)
                   (with-ca/dr (next rest) rest
                     (unless (or (null rest)
                                 (member (car rest) '(&key &aux)))
                       (error 'invalid-lambda-list
                              :datum *lambda-list*))
                     (multiple-value-bind (vars% forms% rest-var%)
                         (parse-&rest next tail)
                       (setq vars  (append vars vars%)
                             forms (append forms forms%)
                             rest-var rest-var%
                             max-length nil
                             lambda-list (cons nil rest)))))
                  ((&key)
                   (if rest-var
                     (setq state '&key
                           tail  rest-var)
                     (setq lambda-list (list* nil '&rest (gensym "all-keyargs-") lambda-list))))
                  ((&allow-other-keys))
                  ((&aux)))
                (multiple-value-bind (vars% forms% tail% min+ max+)
                    (funcall (or (cdr (assoc state *state/parser-alist*))
                                 (error "No parser found for state `~S'."
                                        state))
                             x tail)
                  (setq vars  (append vars vars%)
                        forms (append forms forms%)
                        tail  tail%
                        min-length (+ min-length min+)
                        max-length (if (and (numberp max-length)
                                            (numberp max+))
                                     (+ max-length max+)
                                     nil)))))))
        (let ((whole-form `(%assert-list-length
                            ,form ,min-length ,max-length)))
          (values vars (cons whole-form forms)))))))


(defun parse-&required (param form)
  (multiple-value-bind (vars forms)
      (if (consp param)
        (parse-lambda-list param `(car ,form))
        (values (list param) (list `(car ,form))))
    (values vars forms `(cdr ,form) 1 1)))

(defun parse-&optional (param form)
  (multiple-value-bind (var default sp-var)
      (if (consp param)
        (values (first param) (second param) (third param))
        (values param))
    (let* ((sp-var (or sp-var (gensym "supplied-p-")))
           (form%  `(if ,sp-var (car ,form) ,default)))
      (if (consp var)
        (multiple-value-bind (vars% forms%)
            (parse-lambda-list var form%)
          (values (list* sp-var vars%)
                  (list* `(not (null ,form)) forms%)
                  `(cdr ,form)
                  0 1))
        (values (list sp-var var)
                (list `(not (null ,form)) form%)
                `(cdr ,form)
                0 1)))))

(defun parse-&rest (param form)
  (if (consp param)
    (let ((rest-var (gensym "rest-")))
      (multiple-value-bind (vars forms)
          (parse-lambda-list param rest-var)
        (values (cons rest-var vars)
                (cons form forms)
                rest-var)))
    (values (list param) (list form) param)))

(defun parse-&key (param form)
  (labels ((keyword (name)
             (intern (string name) :keyword)))
    (multiple-value-bind (key-symbol var default sp-var)
        (if (consp param)
          (with-places (first second third) param
            (if (consp first)
              (values (first first) (second first) second third)
              (values (keyword first) first second third)))
          (values (keyword param) param))
      (let* ((sp-var   (or sp-var (gensym "keyarg-supplied-p-")))
             (sp-form  `(get-properties ,form '(,key-symbol)))
             (val-form `(if ,sp-var (getf ,form ',key-symbol) ,default)))
        (multiple-value-bind (vars forms)
            (if (consp var)
              (let ((sublist-var (gensym "keyarg-")))
                (multiple-value-bind (vars forms)
                    (parse-lambda-list var sublist-var)
                  (values (list* sp-var  sublist-var vars)
                          (list* sp-form val-form    forms))))
              (values (list sp-var  var)
                      (list sp-form val-form)))
          (values vars forms form 0))))))




(defmacro lisp:destructuring-bind (lambda-list expr &body body)
  (multiple-value-bind (vars values)
      (let ((destructuring-bind::*lambda-list* lambda-list))
        (destructuring-bind::parse-lambda-list lambda-list expr))
    `(let* (,@(mapcar #'list vars values))
       ,@body)))
#+xyzzy
(setf (get 'destructuring-bind 'ed:lisp-indent-hook) 2)











;;; destructuring-bind.l ends here.
