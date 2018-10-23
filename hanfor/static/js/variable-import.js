require('gasparesganga-jquery-loading-overlay');
require('bootstrap');
require('bootstrap-confirmation2');
require('datatables.net-bs4');
require('datatables.net-select');
require('jquery-ui/ui/widgets/autocomplete');
require('jquery-ui/ui/effects/effect-highlight');
require('./bootstrap-tokenfield.js');

let var_search_string = sessionStorage.getItem('var_search_string');
let available_types = ['bool', 'int', 'real', 'unknown', 'CONST', 'ENUM', 'ENUMERATOR'];

function load_enumerators_to_modal(var_name, var_import_table) {
    let enum_div = $('#enumerators');
    enum_div.html('');
    let enum_html = '';
    var_import_table.rows( ).every( function () {
        let data = this.data();
        if ((var_name.length < data.name.length) && data.name.startsWith(var_name)) {
            if (typeof(data.result.name) !== 'undefined') {
                enum_html += '<p><code>' + data.name + '</code> : <code>' + data.result.const_val + '</code></p>';
            }
        }
    });

    enum_div.html(enum_html);
}


function load_constraints_to_container(var_object, constraints_container) {
    if (var_object.constraints.length > 0) {
        let constraints_list_dom = $('#constraints_list');
        let constraints_html = '';
        var_object.constraints.forEach(function (constraint) {
            constraints_html += '<pre>' + constraint + '</pre>';
        });
        constraints_list_dom.html(constraints_html);
        constraints_container.show();
    }
}


function load_modal(data, var_import_table, type) {
    let var_view_modal = $('#variable_modal');
    let var_value_form = $('#variable_value_form_group');
    let enum_controls = $('.enum-controls');
    let constraints_container = $('#constraints_container');
    let var_object = Object();
    let type_input = $('#variable_type');
    let variable_value = $('#variable_value');
    let save_variable_modal = $('#save_variable_modal');
    let title = '';


    type_input.prop('disabled', true);
    variable_value.prop('disabled', true);
    save_variable_modal.hide();
    if (type === 'source') {
        var_object = data.source;
        title = 'Source Variable:';
    } else if (type === 'target') {
        var_object = data.target;
        title = 'Target Variable:';
    } else {
        title = 'Resulting Variable:';
        var_object = data.result;
        type_input.prop('disabled', false);
        variable_value.prop('disabled', false);
        save_variable_modal.show();
    }

    type_input.autocomplete({
        minLength: 0,
        source: available_types
    }).on('focus', function() { $(this).keydown(); });

    // Prepare modal
    $('#variable_modal_title').html(title + ' <code>' + data.name + '</code>');
    save_variable_modal.attr('data-name', data.name);
    type_input.val(var_object.type);
    var_value_form.hide();
    enum_controls.hide();
    constraints_container.hide();


    if (var_object.type === 'CONST' || var_object.type === 'ENUMERATOR') {
        var_value_form.show();
        variable_value.val(var_object.const_val);
        //variable_value_old.val(var_object.const_val);
    } else if (var_object.type === 'ENUM') {
        enum_controls.show();
        $('#enumerators').html('');
        load_enumerators_to_modal(var_object.name, var_import_table);
    }

    load_constraints_to_container(var_object, constraints_container);

    // $('#var_view_modal_body').html(body_html);
    var_view_modal.modal('show');
}


function modify_row_by_action(row, action, redraw = true) {
    let data = row.data();
    if (action === 'source') {
        if (typeof(data.source.name) !== 'undefined') {
            data.result = data.source;
            data.action = 'source';
        }
    } else if (action === 'target') {
        if (typeof(data.target.name) !== 'undefined') {
            data.result = data.target;
            data.action = 'target';
        }
    } else if (action === 'skip') {
        data.result = data.target;
        data.action =  (typeof(data.target.name) !== 'undefined' ? 'target' : 'skipped');
    }
    if (redraw) {
        row.data(data).draw('full-hold');
    }
}


function get_selected_vars(variables_table) {
    let selected_vars = [];
    variables_table.rows( {selected:true} ).every( function () {
        let d = this.data();
        selected_vars.push(d['name']);
    });
    return selected_vars;
}


function apply_multiselect_action(var_import_table, action) {
    var_import_table.rows( {selected:true} ).every( function () {
        modify_row_by_action(this, action);
    });
}


function store_modal(var_table, target_row) {
    let var_view_modal = $('#variable_modal');
    let type_by_modal = $('#variable_type').val();
    let value_by_modal = $('#variable_value').val();
    let table_data = target_row.data();
    // First check if we have changes.
    let changes = false;
    if (table_data.result.type !== type_by_modal) {
        changes = true;
        table_data.result.type = type_by_modal;
    }
    if ((table_data.result.type === 'CONST' || table_data.result.type === 'ENUMERATOR') &&
        (table_data.result.const_val !== value_by_modal)) {
        changes = true;
        table_data.result.const_val = value_by_modal;
    }
    if (changes) {
        table_data.action = 'custom';
        console.log(table_data);
        // Sync with backend.
        var_view_modal.LoadingOverlay('show');
        $.post( "api/" + session_id + "/store_variable",
            {
                row: JSON.stringify(table_data)
            },
            // Update var table on success or show an error message.
            function( data ) {
                var_view_modal.LoadingOverlay('hide', true);
                if (data['success'] === false) {
                    alert(data['errormsg']);
                } else {
                    target_row.data(table_data).draw('full-hold');
                    $(target_row.node()).effect("highlight", {color: 'green'}, 800);
                    var_view_modal.modal('hide');
                }
        });
    } else {
        var_view_modal.modal('hide');
    }
}


function store_changes(var_import_table) {
    // Fetch relevant changes
    let data = Object();
    var_import_table.rows( ).every( function () {
        let row = this.data();
        data[row.name] = {
            action: row.action,
            result: row.result
        };
    });
    data = JSON.stringify(data);

    // Send changes to backend.
    $.post( "api/" + session_id + "/store_table",
        {
            rows: data
        },
        // Update requirements table on success or show an error message.
        function( data ) {
            if (data['success'] === false) {
                alert(data['errormsg']);
            } else {
                location.reload();
            }
    });
}


function apply_tools_action(var_import_table, action) {
    if (action === 'store-changes') {
        store_changes(var_import_table);
    }
}


$(document).ready(function() {
    // Prepare and load the variables table.
    let var_import_table = $('#var_import_table').DataTable({
        "paging": true,
        "stateSave": true,
        "select": {
            style:    'os',
            selector: 'td:first-child'
        },
        "pageLength": 200,
        "responsive": true,
        "lengthMenu": [[10, 50, 100, 500, -1], [10, 50, 100, 500, "All"]],
        "dom": 'rt<"container"<"row"<"col-md-6"li><"col-md-6"p>>>',
        "ajax": "api/" + session_id + "/get_table_data",
        "deferRender": true,
        "rowId": 'name',
        "columns": [
            {
                // The mass selection column.
                "orderable": false,
                "className": 'select-checkbox',
                "targets": [0],
                "data": null,
                "defaultContent": ""
            },
            {
                // The actions column.
                "data": function ( row, type, val, meta ) {
                    return row;
                },
                "targets": [1],
                "orderable": false,
                "render": function ( data, type, row, meta ) {
                    let result = '<div class="btn-group" role="group" aria-label="Basic example">'
                        + '<button type="button" data-action="skip" class="skip-btn btn btn-secondary'
                        + (data.action === 'skipped' ? ' active' : '') + '">Skip</button>'
                        + '<button type="button" data-action="source" class="source-btn btn btn-secondary'
                        + (data.action === 'source' ? ' active' : '') + '">Source</button>'
                        + '<button type="button" data-action="target" class="target-btn btn btn-secondary'
                        + (data.action === 'target' ? ' active' : '') + '">Target</button>'
                        + '<button type="button" data-action="custom" class="custom-btn btn btn-secondary'
                        + (data.action === 'custom' ? ' active' : '') + '">Custom</button>'
                        + '</div>';
                    return result;
                }
            },
            {
                // The attributes column.
                "data": function ( row, type, val, meta ) {
                    return row;
                },
                "targets": [1],
                "render": function ( data, type, row, meta ) {
                    let result = ``;
                    if (typeof(data.source.name) !== 'undefined' && typeof(data.target.name) !== 'undefined') {
                        result += '<span class="badge badge-info">match_in_source_and_target</span>'
                        if (data.source.type !== data.target.type) {
                            result += '<span class="badge badge-info">unmatched_types</span>'
                        } else {
                            result += '<span class="badge badge-info">same_types</span>'
                        }
                    } else if (typeof(data.source.type) === 'undefined') {
                        result += '<span class="badge badge-info">no_match_in_source</span>'
                    } else if (typeof(data.target.name) === 'undefined') {
                        result += '<span class="badge badge-info">no_match_in_target</span>'
                    }
                    return result;
                }
            },
            {
                // The source column.
                "data": function ( row, type, val, meta ) {
                    return row.source;
                },
                "targets": [3],
                "render": function ( data, type, row, meta ) {
                    let result = '';
                    if (typeof(data.name) !== 'undefined') {
                        result = '<p class="var_link" data-type="source" style="cursor: pointer"><code>' +
                            data.name + '</code> <span class="badge badge-info">' + data.type + '</span></p>';
                    } else {
                        result = 'No match.'
                    }
                    return result;
                }
            },
            {
                // The target column.
                "data": function ( row, type, val, meta ) {
                    return row.target;
                },
                "targets": [4],
                "order": 'asc',
                "render": function ( data, type, row, meta ) {
                    let result = '';
                    if (typeof(data.name) !== 'undefined') {
                        result = '<p class="var_link" data-type="target" style="cursor: pointer"><code>' +
                            data.name + '</code><span class="badge badge-info">' + data.type + '</span>';
                    } else {
                        result = 'No match.'
                    }
                    return result;
                }

            },
            {
                // The result column.
                "data": function ( row, type, val, meta ) {
                    return row.result;
                },
                "targets": [5],
                "render": function ( data, type, row, meta ) {
                    let result = '';
                    if (typeof(data.name) !== 'undefined') {
                        result = '<p class="var_link" data-type="result" style="cursor: pointer"><code>' +
                            data.name + '</code><span class="badge badge-info">' + data.type + '</span>';
                    } else {
                        result = 'Skipped.'
                    }
                    return result;
                }
            }
        ],
        initComplete : function() {
            $('#search_bar').val(var_search_string);
        }
    });

    // Bind big custom searchbar to search the table.
    $('#search_bar').keyup(function(){
      var_import_table.search($(this).val()).draw();
      sessionStorage.setItem('var_search_string', $(this).val());
    });


    let var_import_table_body = $('#var_import_table tbody');

    // Add listener for variable link to modal.
    var_import_table_body.on('click', '.var_link', function (event) {
        // prevent body to be scrolled to the top.
        event.preventDefault();
        let data = var_import_table.row( $(this).parents('tr') ).data();
        let type = $(this).attr('data-type');
        load_modal(data, var_import_table, type);
    });
    
    $('#save_variable_modal').click(function () {
        let name = $(this).attr('data-name');
        let row = var_import_table.row('#' + name);
        store_modal(var_import_table, row);
    });

    $('#variable_type').on('change, focusout, keyup', function () {
        let var_value_form = $('#variable_value_form_group');
        if (['CONST', 'ENUMERATOR'].includes($( this ).val())) {
            var_value_form.show();
        } else {
            var_value_form.hide();
        }
    });

    // Add listener for table row action buttons.
    var_import_table_body.on('click', '.target-btn, .source-btn, .skip-btn', function (event) {
        // prevent body to be scrolled to the top.
        event.preventDefault();
        let row = var_import_table.row( $(this).parents('tr') );
        let action = $(this).attr('data-action');
        modify_row_by_action(row, action);
    });

    // Multiselect. Select single rows.
    $('.select-all-button').on('click', function (e) {
        // Toggle selection on
        if ($( this ).hasClass('btn-secondary')) {
            var_import_table.rows( {page:'current'} ).select();
        }
        else { // Toggle selection off
            var_import_table.rows( {page:'current'} ).deselect();
        }
        // Toggle button state.
        $('.select-all-button').toggleClass('btn-secondary btn-primary');
    });

    // Multiselect action buttons
    $('.action-btn').click(function (e) {
        apply_multiselect_action(var_import_table, $(this).attr('data-action'));
    });

    // Tools Buttons
    $('.tools-btn').click(function (e) {
        let action = $(this).attr('data-action');
        apply_tools_action(var_import_table, action);
    });

    // Toggle "Select all rows to `off` on user specific selection."
    var_import_table.on( 'user-select', function ( ) {
        let select_buttons = $('.select-all-button');
        select_buttons.removeClass('btn-primary');
        select_buttons.addClass('btn-secondary ');
    });

} );