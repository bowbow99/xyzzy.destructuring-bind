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

;; * Debug flag
(defvar *debugging* nil)

(when *debugging*
  (pushnew :debug *features*))

;;;;
;;;; * Utilities

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
                       (if (consp place)
                         `(,(first place) (,(second place) #1#))
                         `(,place (,place #1#))))
               places))
       ,@body)))
#+xyzzy
(setf (get 'with-places 'ed:lisp-indent-hook) 2)

;; modified version of http://paste.lisp.org/display/24480
(defun proper-list-p (object)
  (if (null object) t
    (and (listp object)
         (do ((fast (cdr object) (cddr fast))
              (slow object (cdr slow)))
             ()
           (cond ((null fast) (return t))
                 ((atom fast) (return nil))
                 ((null (cdr fast)) (return t))
                 ((atom (cdr fast)) (return nil))
                 ((eql fast slow) (return nil)))))))

(defparameter *destructuring-lambda-list-keywords*
  (list &optional &rest &key &aux &body &whole &environment &allow-other-keys))

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
    (&rest     . parse-&rest)
    (&body     . parse-&rest)
    (&key      . parse-&key)
    ))

(defparameter *lambda-list* nil)

(defparameter *whole-form-placeholder* nil)
(defparameter *whole-form* nil)
(defparameter *max-length* nil)
(defparameter *min-length* nil)

(defparameter *rest-form* nil)
(defparameter *rest-form-placeholder* nil)
(defparameter *rest-var* nil)

(defparameter *keyword-arguments-p* nil)
(defparameter *known-keywords* nil)
(defparameter *allow-other-keys-p* nil)

(defun parse-lambda-list (lambda-list form)
  (declare (type list lambda-list))
  (multiple-value-bind (whole-var lambda-list)
      (if (eql (car lambda-list) '&whole)
        (values (second lambda-list) (cddr lambda-list))
        (values (gensym "whole-")    lambda-list))
    (let* ((vars  (list whole-var))
           (*whole-form-placeholder* (gensym "$WHOLE-FORM-"))
           (*whole-form* form)
           (*min-length* 0)
           (*max-length* 0)
           (forms (list *whole-form-placeholder*))
           (tail  whole-var)
           (state '&required)
           (*rest-var* nil)
           (*rest-form-placeholder* nil)
           (*rest-form* nil)
           (*keyword-arguments-p* nil)
           (*allow-other-keys-p* nil)
           (*known-keywords* nil))
      (progn
        (do ((lambda-list lambda-list (cdr lambda-list)))
            ((null lambda-list))
          (if (symbolp lambda-list)
            ; lambda-list was a dotted-list
            (setq lambda-list (list nil '&rest lambda-list))
            (with-ca/dr (x rest) lambda-list
              (if (member x *destructuring-lambda-list-keywords*)
                (case x
                  ((&optional &rest &body &key)
                   (setq state x))
                  ((&allow-other-keys))
                  ((&aux)))
                (multiple-value-bind (vars% forms% tail%)
                    (funcall (or (cdr (assoc state *state/parser-alist*))
                                 (error "No parser found for state `~S'."
                                        state))
                             x tail)
                  (setq vars  (append vars vars%)
                        forms (append forms forms%)
                        tail  tail%))))))
        (setq forms (nsubst `(%assert-list-length ,*whole-form* ,*min-length* ,*max-length*)
                            *whole-form-placeholder* forms)
              forms (nsubst *rest-form* *rest-form-placeholder* forms))
        #+debug (break "keywords: ~S" *known-keywords*)
        (values vars forms)))))


(defun parse-&required (param form)
  (multiple-value-bind (vars forms)
      (if (consp param)
        (parse-lambda-list param `(car ,form))
        (values (list param) (list `(car ,form))))
    (incf *min-length*)
    (incf *max-length*)
    (values vars forms `(cdr ,form))))

(defun parse-&optional (param form)
  (multiple-value-bind (var default sp-var)
      (if (consp param)
        (values-list param)
        param)
    (let* ((sp-var  (or sp-var (gensym "supplied-p-")))
           (sp-form `(not (null ,form)))
           (form%   `(if ,sp-var (car ,form) ,default)))
      (multiple-value-bind (vars forms)
          (if (consp var)
            (parse-lambda-list var form%)
            (values (list var) (list form%)))
        (incf *max-length*)
        (values (list* sp-var  vars)
                (list* sp-form forms)
                `(cdr ,form))))))

(defun parse-&rest (param form)
  (when *rest-var*
    (error 'invalid-lambda-list :datum *lambda-list*))
  (let ((rest-var (if (consp param)
                    (gensym "rest-")
                    param)))
    (multiple-value-bind (vars forms)
        (if (consp param)
          (parse-lambda-list param rest-var))
      (setf *max-length* nil
            *rest-var*   rest-var
            *rest-form-placeholder* (gensym "$REST-FORM-")
            *rest-form*  form)
      ;; `*rest-form-placeholder*` will be replaced with form stored
      ;; in `*rest-form*`.
      (values (list* rest-var vars)
              (list* *rest-form-placeholder* forms)
              rest-var))))

(defun parse-&key (param form)
  (labels ((keyword (name)
             (intern (string name) :keyword)))
    (multiple-value-bind (*vars *forms)
        (when (null *rest-var*)
          ;; NOTE: When &key started without &rest, use GENSYM as rest-var.
          (let ((rest-var (gensym "all-keyargs-")))
            (multiple-value-prog1
                (values (list rest-var) (list form))
              (setf *rest-var*   rest-var
                    *max-length* nil
                    form         rest-var))))
      (multiple-value-bind (keyword var default sp-var)
          (if (consp param)
            (with-places ((key/var first) (default second) (sp-var third)) param
              (if (consp key/var)
                (values (first key/var)   (second key/var) default sp-var)
                (values (keyword key/var) key/var          default sp-var)))
            (values (keyword param) param))
        (let* ((sp-var     (or sp-var (gensym "keyarg-supplied-p-")))
               (sp-form    `(get-properties ,form '(,keyword)))
               (value-form `(if ,sp-var (getf ,form ',keyword) ,default)))
          (multiple-value-bind (vars forms)
              (if (consp var)
                (let ((sublist-var (gensym "keyarg-sublist-")))
                  (multiple-value-bind (vars forms)
                      (parse-lambda-list var sublist-var)
                    (values (list* sp-var  sublist-var vars)
                            (list* sp-form value-form  forms))))
                (values (list sp-var  var)
                        (list sp-form value-form)))
            (setf *keyword-arguments-p* t
                  *known-keywords* (cons keyword *known-keywords*))
            (values (append *vars  vars)
                    (append *forms forms)
                    *rest-var*)))))))


(defmacro lisp:destructuring-bind (lambda-list expr &body body)
  (multiple-value-bind (vars values)
      (let ((destructuring-bind::*lambda-list* lambda-list))
        (destructuring-bind::parse-lambda-list lambda-list expr))
    `(let* (,@(mapcar #'list vars values))
       ,@body)))
#+xyzzy
(setf (get 'destructuring-bind 'ed:lisp-indent-hook) 2)







#+debug
(setf *features* (delete :debug *features*))



;;; destructuring-bind.l ends here.
