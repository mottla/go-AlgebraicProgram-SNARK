package utils

// Copyright 2017 Google Inc. All Rights Reserved.
// modified by mottla for the purpose of handling arrays, where most entries are 0
// this sparse array datastructure is a avl self balancing tree, where the keys are the array index
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//     http://www.apache.org/licenses/LICENSE-2.0
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

import (
	"container/list"
	"fmt"
	"math/big"
	"strings"
	"sync"
)

// Comparable is an interface used to pass compare functions to this avltree
type Comparable func(c1 interface{}, c2 interface{}) bool

// EachFunc is an interface used to pass a function to the each() method
type EachFunc func(node *TreeNode, vals ...interface{})

// SparseArray represents a tree
type SparseArray struct {
	root *TreeNode
	lock sync.RWMutex
}

type Entry struct {
	Key   uint
	Value *big.Int
}

// TreeNode represents a node in a tree
type TreeNode struct {
	left   *TreeNode
	right  *TreeNode
	Key    uint
	Value  *big.Int
	height int64
}

func (s TreeNode) String() string {
	return fmt.Sprintf("(%v,%v)", s.Key, s.Value.String())
}

func isSmaler(a, b uint) bool {
	if a < b {
		return true
	}
	return false
}

// Degree gives returns the maximum of a and b
func max(a, b int64) int64 {
	if a > b {
		return a
	}
	return b
}

// getHeight return the height of tree with root `root`
func (root *TreeNode) getHeight() int64 {
	if root != nil {
		return root.height
	}
	return -1
}

// search searches element with Key `Key` in tree with root `root`
// in case the searched element doesn't exist nil is returned
func (root *TreeNode) search(key uint) *TreeNode {
	if root.Key == key {
		return root
	}

	if isSmaler(key, root.Key) {
		if root.left == nil {
			return nil
		}
		return root.left.search(key)
	}

	if root.right == nil {
		return nil
	}
	return root.right.search(key)
}

// getBalance return difference of height of left and right
// subtrees of tree with root `root`
func (root *TreeNode) getBalance() int64 {
	if root == nil {
		return 0
	}
	return root.left.getHeight() - root.right.getHeight()
}

// leftRotate rotates tree with root `root` to the left and
// returns it's new root
func (root *TreeNode) leftRotate() *TreeNode {
	node := root.right
	root.right = node.left
	node.left = root

	root.height = max(root.left.getHeight(), root.right.getHeight()) + 1
	node.height = max(node.right.getHeight(), node.left.getHeight()) + 1
	return node
}

// leftRightRotate performs a left-right rotation of tree with root
// `root` and returns it's new root
func (root *TreeNode) leftRightRotate() *TreeNode {
	root.left = root.left.leftRotate()
	return root.rightRotate()
}

// rightRotate performs a right rotation of tree with root `root`
// and returns it's new root
func (root *TreeNode) rightRotate() *TreeNode {
	node := root.left
	if node == nil {
		fmt.Println("sdaf")
	}
	root.left = node.right
	node.right = root
	root.height = max(root.left.getHeight(), root.right.getHeight()) + 1
	node.height = max(node.left.getHeight(), node.right.getHeight()) + 1
	return node
}

// rightLeftRotate preforms a right-left rotation of tree with root
// `root` and returns it's new root
func (root *TreeNode) rightLeftRotate() *TreeNode {
	root.right = root.right.rightRotate()
	return root.leftRotate()
}

// delete deletes node with Key `Key` from tree. If necessary rebalancing
// is done and new root is returned
func (root *TreeNode) delete(key uint) *TreeNode {
	if root == nil {
		return root
	}

	if isSmaler(key, root.Key) {
		if root.left == nil {
			//fmt.Println("asdf")
		}
		root.left = root.left.delete(key)
	} else if key == root.Key {
		if root.left == nil && root.right == nil {
			return nil
		} else if root.left == nil {
			return root.right
		} else if root.right == nil {
			return root.left
		}

		tmp := root.minNode()
		root.Key = tmp.Key
		root.Value = tmp.Value
		root.right = root.right.delete(tmp.Key)
		root.left = root.left.delete(tmp.Key)
		root.height = max(root.left.getHeight(), root.right.getHeight()) + 1
		balance := root.getBalance()
		if balance > 1 {
			if root.left.getBalance() >= 0 {
				return root.rightRotate()
			}
			return root.leftRightRotate()
		} else if balance < -1 {
			if root.right.getBalance() <= 0 {
				return root.leftRotate()
			}
			return root.rightLeftRotate()
		}
	} else {
		root.right = root.right.delete(key)
	}

	return root
}

// isEqual is a generic function that compares a and b of any comparable type
// return true if a and b are equal, otherwise false
func isEqual(a interface{}, b interface{}) bool {
	return a == b
}

// NewSparseArray simply returns a new (empty) tree
func NewSparseArray() SparseArray {
	return SparseArray{}
}

func NewSparseArrayWith(key uint, value *big.Int) (sp SparseArray) {
	sp.InsertNoOverwriteAllowed(key, value)
	return
}

func NewSparseArrayFromArray(in []*big.Int) SparseArray {
	sp := NewSparseArray()
	for k, v := range in {
		if v.Cmp(bigZero) != 0 {
			sp.InsertNoOverwriteAllowed(uint(k), v)
		}
	}
	return sp
}

//func (t *SparseArray) Sub(key uint, value *big.Int) (_ *TreeNode, err error) {
//	return t.Add(key, new(big.Int).Neg(value))
//}
//
//var addInsert = func(o,n *big.Int)*big.Int {
//	return new(big.Int).Add(o,n)
//}
var setInsert = func(old, new *big.Int) *big.Int {
	return new
}
var setInsertNoOvreride = func(old, new *big.Int) *big.Int {
	if old != nil && old.Cmp(bigZero) != 0 {
		panic("no override")
	}
	return new
}

// Add inserts an element to tree with root `t`
func (t *SparseArray) InsertNoOverwriteAllowed(key uint, value *big.Int) (new *TreeNode, err error) {
	return t.push(key, value, setInsertNoOvreride)
}

//
// Add inserts an element to tree with root `t`
func (t *SparseArray) Insert(key uint, value *big.Int) (new *TreeNode, err error) {
	return t.push(key, value, setInsert)
}

//
//// Add inserts an element to tree with root `t`
//func (t *SparseArray) Add(key uint, value *big.Int) (new *TreeNode, err error) {
//	return t.push(key,value,addInsert)
//}

// Add inserts an element to tree with root `t`
func (t *SparseArray) push(key uint, value *big.Int, insertMode func(old, new *big.Int) *big.Int) (new *TreeNode, err error) {
	if t == nil {
		return nil, fmt.Errorf("unable to insert into nil tree")
	}

	if value.Cmp(bigZero) == 0 {
		return t.root, nil
	}

	t.lock.Lock()
	defer t.lock.Unlock()
	t.root, new = t.root.insert(key, value, insertMode)
	if new.Value.Cmp(bigZero) == 0 {
		t.root = t.root.delete(new.Key)
		return t.root, nil
	}
	return new, nil
}

// insert inserts an element into tree with root `root`
func (root *TreeNode) insert(key uint, value *big.Int, insertMode func(old, new *big.Int) *big.Int) (*TreeNode, *TreeNode) {
	if root == nil {
		root = &TreeNode{
			left:   nil,
			right:  nil,
			Key:    key,
			Value:  insertMode(new(big.Int).SetInt64(0), value),
			height: 0,
		}
		return root, root
	}

	if isEqual(key, root.Key) {
		root.Value = insertMode(root.Value, value)
		return root, root
	}

	var newNode *TreeNode
	if isSmaler(key, root.Key) {
		root.left, newNode = root.left.insert(key, value, insertMode)
		if root.left.getHeight()-root.right.getHeight() == 2 {
			if isSmaler(key, root.left.Key) {
				root = root.rightRotate()
			} else {
				root = root.leftRightRotate()
			}
		}
		list.New()
	} else {
		//root.right, newNode = root.right.insert(key, value, insertMode)
		//if root.right.getHeight()-root.left.getHeight() == 2 {
		//	if (!isSmaler(key, root.right.Key)) && !isEqual(key, root.right.Key) {
		//		root = root.leftRotate()
		//	} else {
		//		root = root.rightLeftRotate()
		//	}
		//}
		root.right, newNode = root.right.insert(key, value, insertMode)
		if root.right.getHeight()-root.left.getHeight() == 2 {
			if isSmaler(root.right.Key, key) {
				root = root.leftRotate()
			} else {
				root = root.rightLeftRotate()
			}
		}
	}

	root.height = max(root.left.getHeight(), root.right.getHeight()) + 1
	return root, newNode
}

// Exists checks if a node with Key `Key` exists in tree `t`
func (t *SparseArray) Exists(key uint) (bool, *big.Int) {
	if t == nil {
		return false, nil
	}
	return t.root.exists(key)
}

// exists recursively searches through tree with root `root` for element with
// Key `Key`
func (root *TreeNode) exists(key uint) (bool, *big.Int) {
	if root == nil {
		return false, nil
	}

	if key == root.Key {
		return true, root.Value
	}

	if isSmaler(key, root.Key) {
		if root.left == nil {
			return false, nil
		}
		return root.left.exists(key)
	}
	if root.right == nil {
		return false, nil
	}
	return root.right.exists(key)
}

// MaxNode returns the node with the maximal Key in the tree
func (t *SparseArray) Degree() uint {
	if t == nil {
		return 0
	}
	return t.root.maxNode().Key
}

// MaxNode returns the node with the maximal Key in the tree
func (t *SparseArray) MaxNode() *TreeNode {
	if t == nil {
		return nil
	}
	return t.root.maxNode()
}
func (root *TreeNode) maxNode() (t *TreeNode) {
	if root == nil {
		return nil
	}
	if root.right != nil {
		return root.right.maxNode()
	}
	return root
}

// MinNode returns the node with the minimal Key in the tree
func (t *SparseArray) MinNode() *TreeNode {
	if t == nil {
		return &TreeNode{
			Key: 0,
		}
	}
	return t.root.minNode()
}
func (root *TreeNode) minNode() (t *TreeNode) {
	if root == nil {
		return nil
	}
	if root.left != nil {
		return root.left.minNode()
	}
	return root
}

// Each recursively traverses tree `tree` and collects all nodes
// array is filled up from highest to lowest degree
func (t *SparseArray) ChannelNodes(ascendingOrder bool) (collectedNodes chan Entry) {

	t.lock.RLock()

	collectedNodes = make(chan Entry)
	if ascendingOrder {
		go func() {
			t.root.channelNodesAscending(collectedNodes)
			close(collectedNodes)
			t.lock.RUnlock()
		}()
		return
	}

	go func() {
		t.root.channelNodesDescending(collectedNodes)
		close(collectedNodes)
		t.lock.RUnlock()
	}()
	return
}

// Each recursively traverses tree `tree` and collects all nodes
func (root *TreeNode) channelNodesAscending(collectedNodes chan Entry) {
	if root == nil {
		return
	}

	if root.left != nil {
		root.left.channelNodesAscending(collectedNodes)
	}
	collectedNodes <- Entry{
		Key:   root.Key,
		Value: root.Value,
	}
	if root.right != nil {
		root.right.channelNodesAscending(collectedNodes)
	}

}

// Each recursively traverses tree `tree` and collects all nodes
func (root *TreeNode) channelNodesDescending(collectedNodes chan Entry) {
	if root == nil {
		return
	}

	if root.right != nil {
		root.right.channelNodesDescending(collectedNodes)
	}
	collectedNodes <- Entry{
		Key:   root.Key,
		Value: root.Value,
	}
	if root.left != nil {
		root.left.channelNodesDescending(collectedNodes)
	}

}

// MaxNode returns the node with the maximal Key in the tree
func (t *SparseArray) Count() int {
	if t == nil {
		return 0
	}
	return t.root.count()
}
func (root *TreeNode) count() int {
	if root == nil {
		return 0
	}
	var i = 1
	if root.right != nil {
		i += root.right.count()
	}
	if root.left != nil {
		i += root.left.count()
	}
	return i
}

// Each recursively traverses tree `tree` and collects all nodes
// array is filled up from highest to lowest degree
func (t *SparseArray) String() string {
	if t == nil {
		return "empty"
	}
	t.lock.RLock()
	defer t.lock.RUnlock()
	sb := new(strings.Builder)
	t.root.print(sb)
	return sb.String()
}

// Each recursively traverses tree `tree` and collects all nodes
func (root *TreeNode) print(sb *strings.Builder) {
	if root == nil {
		return
	}

	if root.right != nil {
		root.right.print(sb)
	}
	sb.WriteString(root.String())
	if root.left != nil {
		root.left.print(sb)
	}

}

// Each recursively traverses tree `tree` and collects all nodes
// array is filled up from highest to lowest degree
func (t *SparseArray) DecendingNodes() (collectedNodes []Entry) {
	if t == nil {
		return nil
	}
	t.lock.RLock()
	defer t.lock.RUnlock()
	t.root.AllNodes(&collectedNodes)
	return
}

// Each recursively traverses tree `tree` and collects all nodes
func (root *TreeNode) AllNodes(t *[]Entry) {
	if root == nil {
		return
	}

	if root.right != nil {
		root.right.AllNodes(t)
	}
	(*t) = append((*t), Entry{
		Key:   root.Key,
		Value: root.Value,
	})
	if root.left != nil {
		root.left.AllNodes(t)
	}

}

// Each can be used to traverse tree `t` and call function f with params vals...
// for each node in the tree
func (t *SparseArray) Each(f EachFunc, vals ...interface{}) {
	if t == nil {
		return
	}

	t.lock.RLock()
	defer t.lock.RUnlock()
	t.root.Each(f, vals...)
}

// Each recursively traverses tree `tree` and calls functions f with params vals...
// for each node in the tree
func (root *TreeNode) Each(f EachFunc, vals ...interface{}) {
	if root == nil {
		return
	}
	f(root, vals...)
	if root.left != nil {
		root.left.Each(f, vals...)
	}
	if root.right != nil {
		root.right.Each(f, vals...)
	}
}
