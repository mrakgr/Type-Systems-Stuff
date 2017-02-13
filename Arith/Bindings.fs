module Bindings

open System.Windows
open Microsoft.Win32
open System
open System.IO
open System.Text
open System.Diagnostics
open System.ComponentModel
open System.Windows
open System.Windows.Input
open System.Windows.Controls
open System.Windows.Controls.Primitives
open System.Windows.Media
open System.Windows.Media.Imaging
open System.Windows.Shapes
open System.Windows.Documents
open System.Windows.Threading
open System.Windows.Data

/// Sets the Content propert of ctrl to x
let inline setAsContentFor ctrl x =
    (^a: (member set_Content: obj -> unit) ctrl, x)
    x

/// Adds row definitions to container
let inline addRowDefs (rows: RowDefinition[]) cont =
    for x in rows do
        (^a : (member RowDefinitions: RowDefinitionCollection) cont).Add x
    cont

/// Adds column definitions to container
let inline addColDefs (cols: ColumnDefinition[]) cont =
    for x in cols do
        (^a : (member ColumnDefinitions: ColumnDefinitionCollection) cont).Add x
    cont

/// Appends to the UIElementCollection
let inline addChildren cont child = 
    (^a : (member Children: UIElementCollection) cont).Add child |> ignore
    child

/// Appends to the Grid
let inline addGrid (cont: Grid) row col child = 
    cont.Children.Add child |> ignore
    Grid.SetRow(child,row)
    Grid.SetColumn(child,col)
    child

/// Appends to the Grid. Also has the row span and column span arguments.
let inline addGrid' (cont: Grid) row rowSpan col colSpan child = 
    cont.Children.Add child |> ignore
    Grid.SetRow(child,row)
    Grid.SetRowSpan(child,rowSpan)
    Grid.SetColumn(child,col)
    Grid.SetColumnSpan(child,colSpan)
    child

/// Appends to the Dock
let inline addDock (cont: DockPanel) pos child = 
    cont.Children.Add child |> ignore
    DockPanel.SetDock(child,pos)
    child

/// Appends to the ItemCollection
let inline addItems cont child = 
    (^a : (member Items: ItemCollection) cont).Add child |> ignore
    child

/// Appends to the TabControl
let inline addTabControl (cont: TabControl) head child = 
    let x = TabItem(Header=head, Content=child)
    cont.Items.Add x |> ignore
    child

/// Appends to the Collection
let inline addToolBars cont child = 
    (^a : (member ToolBars: Collections.ObjectModel.Collection<_>) cont).Add child |> ignore
    child

/// Sets a dependency property
let inline setDP (prop: DependencyProperty) (v: obj) target =
    (^a : (member SetValue: DependencyProperty * obj -> unit) (target,prop,v))
    target

/// Sets a binding
let inline setBind (prop: DependencyProperty) (v: string) target =
    (^a : (member SetBinding: DependencyProperty * string -> BindingExpression) (target,prop,v))
    |> ignore
    target

/// Sets a binding
let inline setBind' (prop: DependencyProperty) (v: BindingBase) target =
    (^a : (member SetBinding: DependencyProperty * BindingBase -> unit) (target,prop,v))
    target

type DockPanel with
    /// Sets the Dock property
    static member inline DockTop(x: 'a) = setDP DockPanel.DockProperty Dock.Top x
    /// Sets the Dock property
    static member inline DockBottom(x: 'a) = setDP DockPanel.DockProperty Dock.Bottom x
    /// Sets the Dock property
    static member inline DockLeft(x: 'a) = setDP DockPanel.DockProperty Dock.Left x
    /// Sets the Dock property
    static member inline DockRight(x: 'a) = setDP DockPanel.DockProperty Dock.Right x