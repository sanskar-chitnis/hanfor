""" 

@copyright: 2018 Samuel Roth <samuel@smel.de>
@licence: GPLv3
"""
import argparse
import boogie_parsing
import csv
import datetime
import html
import logging
import os
import re

from flask import json
from flask_assets import Bundle, Environment
from reqtransformer import VarImportSessions, VariableCollection, Requirement, ScriptEvals
from static_utils import pickle_dump_obj_to_file, pickle_load_from_dump, replace_prefix
from typing import Union, Set
from terminaltables import DoubleTable


here = os.path.dirname(os.path.realpath(__file__))
default_scope_options = '''
    <option value="NONE">None</option>
    <option value="GLOBALLY">Globally</option>
    <option value="BEFORE">Before "{P}"</option>
    <option value="AFTER">After "{P}"</option>
    <option value="BETWEEN">Between "{P}" and "{Q}"</option>
    <option value="AFTER_UNTIL">After "{P}" until "{Q}"</option>
    '''
default_pattern_options = '''
    <option value="NotFormalizable">None</option>
    <optgroup label="Occurence">
    <option value="Invariant">it is always the case that if "{R}" holds, then "{S}"
        holds as well</option>
    <option value="Absence">it is never the case that "{R}" holds</option>
    <option value="Universality">it is always the case that "{R}" holds</option>
    <option value="Existence">"{R}" eventually holds</option>
    <option value="BoundedExistence">transitions to states in which "{R}" holds
        occur at most twice</option>
    </optgroup>
    <optgroup label="Order">
    <option value="Precedence">it is always the case that if "{R}" holds then "{S}"
        previously held</option>
    <option value="PrecedenceChain1-2">it is always the case that if "{R}" holds
        and is succeeded by "{S}", then "{T}" previously held</option>
    <option value="PrecedenceChain2-1">it is always the case that if "{R}" holds then "{S}"
        previously held and was preceded by "{T}"</option>
    <option value="Response">it is always the case that if "{R}" holds then "{S}"
        eventually holds</option>
    <option value="ResponseChain1-2">it is always the case that if "{R}" holds then "{S}"
        eventually holds and is succeeded by "{T}"</option>
    <option value="ResponseChain2-1">it is always the case that if "{R}" holds and is
        succeeded by "{S}", then "{T}" eventually holds after "{S}"</option>
    <option value="ConstrainedChain">it is always the case that if "{R}" holds then "{S}"
        eventually holds and is succeeded by "{T}", where "{U}" does not hold between "{S}" and "{T}"</option>
    </optgroup>
    <optgroup label="Real-time">
    <option value="MinDuration">it is always the case that once "{R}" becomes satisfied,
        it holds for at least "{S}" time units</option>
    <option value="MaxDuration">it is always the case that once "{R}" becomes satisfied,
        it holds for less than "{S}" time units</option>
    <option value="BoundedRecurrence">it is always the case that "{R}" holds at least every
        "{S}" time units</option>
    <option value="BoundedResponse">it is always the case that if "{R}" holds, then "{S}"
        holds after at most "{T}" time units</option>
    <option value="BoundedInvariance">it is always the case that if "{R}" holds, then "{S}"
        holds for at least "{T}" time units</option>
    <option value="TimeConstrainedMinDuration">it is always the case that if {R} holds for at least {S} time units,
        then {T} holds afterwards for at least {U} time units</option>
    <option value="TimeConstrainedInvariant">it is always the case that if {R} holds for at least {S} time units,
        then {T} holds afterwards</option>
    <option value="ConstrainedTimedExistence">it is always the case that if {R} holds,
        then {S} holds after at most {T} time units for at least {U} time units</option>
    <option value="Toggle1">it is always the case that if {R} holds then {S} toggles {T}</option>
    <option value="Toggle2">it is always the case that if {R} holds then {S} toggles {T} at most {U} time units later</option>
    </optgroup>
    <optgroup label="not_formalizable">
    <option value="NotFormalizable">// not formalizable</option>
    </optgroup>
    '''


def get_formalization_template(templates_folder, requirement, formalization_id, formalization):
    result = {'success': True, 'html': formalization_html(
        templates_folder,
        formalization_id,
        default_scope_options,
        default_pattern_options,
        formalization
    )}

    return result


def formalization_html(templates_folder, formalization_id, scope_options, pattern_options, formalization):
    # Load template.
    html_template = ''
    with open(os.path.join(templates_folder, 'formalization.html'), mode='r') as f:
        html_template += '\n'.join(f.readlines())

    # Set values
    html_template = html_template.replace('__formalization_text__', formalization.get_string())
    html_template = html_template.replace('__formal_id__', '{}'.format(formalization_id))
    form_desc = formalization.get_string()
    if len(form_desc) < 10:  # Add hint to open if desc is short.
        form_desc += '... (click to open)'
    html_template = html_template.replace('__formal_desc__', form_desc)

    # Selected scope and pattern:
    if formalization.scoped_pattern is not None:
        scope = formalization.scoped_pattern.get_scope_slug()
        pattern = formalization.scoped_pattern.get_pattern_slug()
        scope_options = scope_options.replace('value="{}"'.format(scope), 'value="{}" selected'.format(scope))
        pattern_options = pattern_options.replace('value="{}"'.format(pattern), 'value="{}" selected'.format(pattern))
    html_template = html_template.replace('__scope_options__', scope_options)
    html_template = html_template.replace('__pattern__options__', pattern_options)

    # Expressions
    for key, value in formalization.expressions_mapping.items():
        html_template = html_template.replace(
            '__expr_{}_content__'.format(key), '{}'.format(html.escape(str(value.raw_expression))))

    # Unset remaining vars.
    html_template = re.sub(r'__expr_._content__', '', html_template)

    return html_template


def formalizations_to_html(app, formalizations):
    result = ''
    for index, formalization in formalizations.items():
        result += formalization_html(
            app.config['TEMPLATES_FOLDER'],
            index,
            default_scope_options,
            default_pattern_options,
            formalization
        )
    return result


def get_available_vars(app, full=True, fetch_evals=False):
    var_collection = VariableCollection.load(app.config['SESSION_VARIABLE_COLLECTION'])
    result = var_collection.get_available_vars_list(used_only=not full)

    if fetch_evals:
        script_results = ScriptEvals.load(path=app.config['SCRIPT_EVAL_RESULTS_PATH']).get_concatenated_evals()
        for variable_data in result:
            if variable_data['name'] in script_results:
                variable_data['script_results'] = script_results[variable_data['name']]

    return result


def varcollection_diff_info(app, request):
    """ Collect diff info of current and requested var collection.
        * Number of var in the requested var collection
        * Number of new vars in the requested var collection.


    :param request: API request
    :return: {'tot_vars': int, 'new_vars': int}
    :rtype: dict
    """
    current_var_collection = VariableCollection.load(app.config['SESSION_VARIABLE_COLLECTION'])
    req_path = os.path.join(
        app.config['SESSION_BASE_FOLDER'],
        request.form.get('sess_name').strip(),
        request.form.get('sess_revision').strip(),
        'session_variable_collection.pickle'
    )
    requested_var_collection = VariableCollection.load(req_path)

    numb_new_vars = len(
        set(requested_var_collection.collection.keys()).difference(current_var_collection.collection.keys())
    )

    result = {
        'tot_vars': len(requested_var_collection.collection),
        'new_vars': numb_new_vars
    }

    return result


def varcollection_create_new_import_session(app, source_session_name, source_revision_name):
    """ Creates a new blank variable collection import session.
    Returns the associated session_id or -1 if the creation fails.

    :param app: Current flask app.
    :param source_session_name:
    :param source_revision_name:
    """
    current_var_collection = VariableCollection.load(app.config['SESSION_VARIABLE_COLLECTION'])
    source_var_collection_path = os.path.join(
        app.config['SESSION_BASE_FOLDER'],
        source_session_name,
        source_revision_name,
        'session_variable_collection.pickle'
    )
    source_var_collection = VariableCollection.load(source_var_collection_path)

    # load import_sessions
    var_import_sessions_path = os.path.join(app.config['SESSION_BASE_FOLDER'], 'variable_import_sessions.pickle')
    try:
        var_import_sessions = VarImportSessions.load(var_import_sessions_path)
    except FileNotFoundError:
        var_import_sessions = VarImportSessions(path=var_import_sessions_path)
        var_import_sessions.store()

    session_id = var_import_sessions.create_new_session(
        source_collection=source_var_collection,
        target_collection=current_var_collection
    )

    return session_id


def update_req_search(app, request, delete=False):
    """ Update a search query.
    A search query will be used as presets for requirements search in the frontend.

    :param delete: If true remove the search query
    """
    search_query = request.form.get('query', '').strip()

    result = {
        'success': True
    }

    if len(search_query) > 0:
        meta_settings = MetaSettings(app.config['META_SETTTINGS_PATH'])
        if not delete:
            # Store the search query into meta settings.
            if 'available_search_strings' not in meta_settings:
                meta_settings['available_search_strings'] = list()
            meta_settings['available_search_strings'].append(search_query)
        elif search_query in meta_settings['available_search_strings']:
            # delete query.
            meta_settings['available_search_strings'].remove(search_query)
        meta_settings.update_storage()

    return result


def get_requirements_using_var(requirements: list, var_name: str):
    """ Return a list of requirement ids where var_name is used in at least one formalization.

    :param requirements: list of Requirement.
    :param var_name: Variable name to search for.
    :return: List of affected Requirement ids.
    """
    result_rids = []
    for requirement in requirements:  # type: Requirement
        if requirement.uses_var(var_name):
            result_rids.append(requirement.rid)

    return result_rids


def update_variable_in_collection(app, request):
    """ Update a single variable. The request should contain a form:
        name -> the new name of the var.
        name_old -> the name of the var before.
        type -> the new type of the var.
        type_old -> the old type of the var.
        occurrences -> Ids of requirements using this variable.
        enumerators -> The dict of enumerators

    :param app: the running flask app
    :type app: Flask
    :param request: A form request
    :type request: flask.Request
    :return: Dictionary containing changed data and request status information.
    :rtype: dict
    """
    # Get properties from request
    var_name = request.form.get('name', '').strip()
    var_name_old = request.form.get('name_old', '').strip()
    var_type = request.form.get('type', '').strip()
    var_type_old = request.form.get('type_old', '').strip()
    var_const_val = request.form.get('const_val', '').strip()
    var_const_val_old = request.form.get('const_val_old', '').strip()
    belongs_to_enum = request.form.get('belongs_to_enum', '').strip()
    belongs_to_enum_old = request.form.get('belongs_to_enum_old', '').strip()
    occurrences = request.form.get('occurrences', '').strip().split(',')
    enumerators = json.loads(request.form.get('enumerators', ''))

    var_collection = VariableCollection.load(app.config['SESSION_VARIABLE_COLLECTION'])
    result = {
        'success': True,
        'has_changes': False,
        'type_changed': False,
        'name_changed': False,
        'rebuild_table': False,
        'data': {
            'name': var_name,
            'type': var_type,
            'used_by': occurrences,
            'const_val': var_const_val
        }
    }

    # Check for changes
    if (
        var_type_old != var_type
        or var_name_old != var_name
        or var_const_val_old != var_const_val
        or request.form.get('updated_constraints') == 'true'
        or belongs_to_enum != belongs_to_enum_old
    ):
        logging.info('Update Variable `{}`'.format(var_name_old))
        result['has_changes'] = True
        reload_type_inference = False

        # Update type.
        if var_type_old != var_type:
            logging.info('Change type from `{}` to `{}`.'.format(var_type_old, var_type))
            try:
                var_collection.collection[var_name_old].belongs_to_enum = belongs_to_enum
                var_collection.set_type(var_name_old, var_type)
            except TypeError as e:
                result = {
                    'success': False,
                    'errormsg': str(e)
                }
                return result
            result['type_changed'] = True
            reload_type_inference = True

        # Update const value.
        if var_const_val_old != var_const_val:
            try:
                if var_type == 'ENUMERATOR_INT':
                    int(var_const_val)
                if var_type in ['ENUMERATOR_REAL']:
                    float(var_const_val)
            except Exception as e:
                result = {
                    'success':  False,
                    'errormsg': 'Enumerator value `{}` for {} `{}` not valid: {}'.format(
                        var_const_val, var_type, var_name, e
                    )
                }
                return result
            logging.info('Change value from `{}` to `{}`.'.format(var_const_val_old, var_const_val))
            var_collection.collection[var_name].value = var_const_val
            result['val_changed'] = True

        # Update constraints.
        if request.form.get('updated_constraints') == 'true':
            constraints = json.loads(request.form.get('constraints', ''))
            logging.debug('Update Variable Constraints')
            try:
                var_collection = var_collection.collection[var_name_old].update_constraints(
                    constraints,
                    app,
                    var_collection
                )
                result['rebuild_table'] = True
            except KeyError as e:
                result['success'] = False
                result['error_msg'] = 'Could not set constraint: Missing expression/variable for {}'.format(e)
            except Exception as e:
                result['success'] = False
                result['error_msg'] = 'Could not parse formalization: `{}`'.format(e)
        else:
            logging.debug('Skipping variable Constraints update.')

        # update name.
        if var_name_old != var_name:
            affected_enumerators = []
            logging.debug('Change name of var `{}` to `{}`'.format(var_name_old, var_name))
            #  Case: New name which does not exist -> remove the old var and replace in reqs ocurring.
            if var_name not in var_collection:
                logging.debug('`{}` is a new var name. Rename the var, replace occurences.'.format(
                    var_name
                ))
                # Rename the var (Copy to new name and remove the old item. Rename it)
                affected_enumerators = var_collection.rename(var_name_old, var_name, app)

            else:  # Case: New name exists. -> Merge the two vars into one. -> Complete rebuild.
                if var_collection.collection[var_name_old].type != var_collection.collection[var_name].type:
                    result['success'] = False
                    result['errormsg'] = 'To merge two variables the types must be identical. {} != {}'.format(
                        var_collection.collection[var_name_old].type,
                        var_collection.collection[var_name].type
                    )
                    return result
                logging.debug('`{}` is an existing var name. Merging the two vars. '.format(var_name))
                # var_collection.merge_vars(var_name_old, var_name, app)
                affected_enumerators = var_collection.rename(var_name_old, var_name, app)
                result['rebuild_table'] = True
                reload_type_inference = True

            # Update the requirements using this var.
            if len(occurrences) > 0:
                rename_variable_in_expressions(app, occurrences, var_name_old, var_name)

            for (old_enumerator_name, new_enumerator_name) in affected_enumerators:
                # Todo: Implement this more eff.
                # Todo: Refactor Formalizations to use hashes as vars and fetch them in __str__ from the var collection.
                requirements = get_requirements(app.config['REVISION_FOLDER'])
                affected_requirements = get_requirements_using_var(requirements, old_enumerator_name)
                rename_variable_in_expressions(
                    app,
                    affected_requirements,
                    old_enumerator_name,
                    new_enumerator_name
                )

            result['name_changed'] = True

        # Change ENUM parent.
        if belongs_to_enum != belongs_to_enum_old and var_type in ['ENUMERATOR_INT', 'ENUMERATOR_REAL']:
            logging.debug('Change enum parent of enumerator `{}` to `{}`'.format(var_name, belongs_to_enum))
            if belongs_to_enum not in var_collection:
                result['success'] = False
                result['errormsg'] = 'The new ENUM parent `{}` does not exist.'.format(
                    belongs_to_enum
                )
                return result
            if var_collection.collection[belongs_to_enum].type != replace_prefix(var_type, 'ENUMERATOR', 'ENUM'):
                result['success'] = False
                result['errormsg'] = 'The new ENUM parent `{}` is not an {} (is `{}`).'.format(
                    belongs_to_enum,
                    replace_prefix(var_type, 'ENUMERATOR', 'ENUM'),
                    var_collection.collection[belongs_to_enum].type
                )
                return result
            new_enumerator_name = replace_prefix(var_name, belongs_to_enum_old, '')
            new_enumerator_name = replace_prefix(new_enumerator_name, '_', '')
            new_enumerator_name = replace_prefix(new_enumerator_name, '', belongs_to_enum + '_')
            if new_enumerator_name in var_collection:
                result['success'] = False
                result['errormsg'] = 'The new ENUM parent `{}` already has a ENUMERATOR `{}`.'.format(
                    belongs_to_enum,
                    new_enumerator_name
                )
                return result

            var_collection.collection[var_name].belongs_to_enum = belongs_to_enum
            var_collection.rename(var_name, new_enumerator_name, app)

        logging.info('Store updated variables.')
        var_collection.refresh_var_constraint_mapping()
        var_collection.store(app.config['SESSION_VARIABLE_COLLECTION'])
        logging.info('Update derived types by parsing affected formalizations.')
        if reload_type_inference and var_name in var_collection.var_req_mapping:
            for rid in var_collection.var_req_mapping[var_name]:
                requirement = Requirement.load_requirement_by_id(rid, app)
                if requirement:
                    requirement.reload_type_inference(var_collection, app)

    if var_type in ['ENUM_INT', 'ENUM_REAL']:
        new_enumerators = []
        for enumerator_name, enumerator_value in enumerators:
            if len(enumerator_name) == 0 and len(enumerator_value) == 0:
                continue
            if len(enumerator_name) == 0 or not re.match('^[a-zA-Z0-9_-]+$', enumerator_name):
                result = {
                    'success': False,
                    'errormsg': 'Enumerator name `{}` not valid'.format(enumerator_name)
                }
                break
            try:
                if var_type == 'ENUM_INT':
                    int(enumerator_value)
                if var_type == 'ENUM_REAL':
                    float(enumerator_value)
            except Exception as e:
                result = {
                    'success':  False,
                    'errormsg': 'Enumerator value `{}` for enumerator `{}` not valid: {}'.format(
                        enumerator_value, enumerator_name, e
                    )
                }
                break

            enumerator_name = '{}_{}'.format(var_name, enumerator_name)
            # Add new enumerators to the var_collection
            if not var_collection.var_name_exists(enumerator_name):
                var_collection.add_var(enumerator_name)
                new_enumerators.append(enumerator_name)

            var_collection.collection[enumerator_name].set_type('ENUMERATOR_{}'.format(var_type[5:]))
            var_collection.collection[enumerator_name].value = enumerator_value
            var_collection.collection[enumerator_name].belongs_to_enum = var_name

        var_collection.store(app.config['SESSION_VARIABLE_COLLECTION'])

        if len(new_enumerators) > 0:
            var_collection.reload_script_results(app, new_enumerators)

    return result


def rename_variable_in_expressions(app, occurences, var_name_old, var_name):
    """ Updates (replace) the variables in the requirement expressioins.

    :param app: Flask app (used for session).
    :type app: Flask
    :param occurences: Requirement ids to be taken into account.
    :type occurences: list (of str)
    :param var_name_old: The current name in the expressions.
    :type var_name_old: str
    :param var_name: The new name.
    :type var_name: str
    """
    logging.debug('Update requirements using old var `{}` to `{}`'.format(var_name_old, var_name))
    for rid in occurences:
        filepath = os.path.join(app.config['REVISION_FOLDER'], '{}.pickle'.format(rid))
        if os.path.exists(filepath) and os.path.isfile(filepath):
            requirement = Requirement.load(filepath)
            # replace in every formalization
            for index, formalization in requirement.formalizations.items():
                for key, expression in formalization.expressions_mapping.items():
                    if var_name_old not in expression.raw_expression:
                        continue
                    new_expression = boogie_parsing.replace_var_in_expression(
                        expression=expression.raw_expression,
                        old_var=var_name_old,
                        new_var=var_name
                    )
                    requirement.formalizations[index].expressions_mapping[key].raw_expression = new_expression
                    requirement.formalizations[index].expressions_mapping[key].used_variables.discard(var_name_old)
                    requirement.formalizations[index].expressions_mapping[key].used_variables.add(var_name)
            logging.debug('Updated variables in requirement id: `{}`.'.format(requirement.rid))
            requirement.store(filepath)


def rename_variable_in_constraints(app, occurences, var_name_old, var_name, variable_collection):
    """ Renames the variable in

    :param app:
    :param occurences:
    :param var_name_old:
    :param var_name:
    :param variable_collection:
    """
    if var_name_old in variable_collection.collection.keys():
        pass


def get_requirements(input_dir, filter_list=None, invert_filter=False):
    """ Load all requirements from session folder and return in a list.

    :param tag: Session tag
    :type tag: str
    :param filter: A list of requirement IDs to be included in the result. All if not set.
    :type filter: list (of strings)
    :param invert_filter: Exclude filter
    :type invert_filter: bool
    """
    filenames = [
        os.path.join(input_dir, f) for f in os.listdir(input_dir)
        if os.path.isfile(os.path.join(input_dir, f))
    ]
    filenames.sort()
    requirements = list()

    def should_be_in_result(req) -> bool:
        if filter_list is None:
            return True
        return (req.rid in filter_list) != invert_filter

    for filename in filenames:
        try:
            req = Requirement.load(filename)
        except TypeError:
            continue
        if hasattr(req, 'rid'):
            if should_be_in_result(req):
                logging.debug('Adding {} to results.'.format(req.rid))
                requirements.append(req)

    return requirements


def generate_csv_file(app, output_file=None, filter_list=None, invert_filter=False):
    """ Generates the csv file for a session by tag.

    :param tag: Session tag
    :type tag: str
    :param output_file: Where to store the file
    :type output_file: str
    :param filter: A list of requirement IDs to be included in the result. All if not set.
    :type filter: list (of strings)
    :param invert_filter: Exclude filter
    :type invert_filter: bool
    :return: Output file location on success.
    :rtype: str
    """
    # Get requirements
    tag_col_name = 'Hanfor_Tags'
    requirements = get_requirements(app.config['REVISION_FOLDER'], filter_list=filter_list, invert_filter=invert_filter)

    # get session status
    session_dict = pickle_load_from_dump(app.config['SESSION_STATUS_PATH'])  # type: dict

    # Generate Output filename.
    if not output_file:
        output_file = os.path.join(app.config['SESSION_FOLDER'], '{}_{}_out.csv'.format(
            app.config['SESSION_TAG'],
            app.config['USING_REVISION']
        ))

    # Add Formalization col if not existent in input CSV.
    for csv_key in [session_dict['csv_formal_header']]:
        if csv_key not in session_dict['csv_fieldnames']:
            session_dict['csv_fieldnames'].append(csv_key)

    # Add Hanfor Tag col to csv.
    while tag_col_name in session_dict['csv_fieldnames']:
        tag_col_name += '_1'
    session_dict['csv_fieldnames'].append(tag_col_name)

    # Collect data.
    for requirement in requirements:
        requirement.csv_row[session_dict['csv_formal_header']] = requirement.get_formalization_string()
        requirement.csv_row[tag_col_name] = ', '.join(requirement.tags)

    # Write data to file.
    rows = [r.csv_row for r in requirements]
    with open(output_file, mode='w') as out_csv:
        csv.register_dialect('ultimate', delimiter=',')
        writer = csv.DictWriter(out_csv, session_dict['csv_fieldnames'], dialect=session_dict['csv_dialect'])
        writer.writeheader()
        writer.writerows(rows)

    return output_file


def clean_identifier_for_ultimate_parser(slug: str, used_slugs: Set[str]) -> (str, Set[str]):
    """ Clean slug to be sound for ultimate parser.

    :param slug: The slug to be cleaned.
    :param used_slugs: Set of already used slugs.
    :return: (save_slug, used_slugs) save_slug a save to use form of slug. save_slug added to used_slugs.
    """
    # Replace any occurence of [whitespace, `.`, `-`] with `_`
    slug = re.sub(r"[\s+.-]+", '_', slug.strip())

    # Resolve illegal start
    slug = re.sub(r"^[^a-zA-Z]", 'ID_', slug)

    # Resolve duplicates
    # search for the first free suffix.
    if slug in used_slugs:
        suffix = 1
        pad = lambda s: '{}_{}'.format(slug, s)
        while pad(suffix) in used_slugs:
            suffix += 1
        slug = pad(suffix)

    used_slugs.add(slug)

    return slug, used_slugs


def generate_req_file(app, output_file=None, filter_list=None, invert_filter=False, variables_only=False):
    """ Generate the ulltimate requirements file.

    :param tag: Session tag
    :type tag: str
    :type output_file: str
    :param filter: A list of requirement IDs to be included in the result. All if not set.
    :type filter: list (of strings)
    :param invert_filter: Exclude filter
    :type invert_filter: bool
    :return: Output file location on success.
    :rtype: str
    """
    logging.info('Generating .req file for session {}'.format(app.config['SESSION_TAG']))
    # Get requirements
    requirements = get_requirements(app.config['REVISION_FOLDER'], filter_list=filter_list, invert_filter=invert_filter)

    var_collection = VariableCollection.load(app.config['SESSION_VARIABLE_COLLECTION'])
    available_vars = []
    if filter_list is not None:
        # Filter the available vars to only include the ones actually used by a requirement.
        logging.info('Filtering the .req file to only include {} selected requirements.'.format(len(filter_list)))
        logging.debug('Only include req.ids: {}.'.format(filter_list))
        target_set = set(filter_list)
        for var in var_collection.get_available_vars_list(sort_by='name'):
            try:
                used_in = var_collection.var_req_mapping[var['name']]
                if used_in & target_set:
                    available_vars.append(var)
            except:
                logging.debug('Ignoring variable `{}`'.format(var))
    else:
        available_vars = var_collection.get_available_vars_list(sort_by='name')

    available_vars = [var['name'] for var in available_vars]

    # Write to .req file
    if not output_file:
        file_suffix = ''
        if variables_only:
            file_suffix = 'variables_only'
        output_file = os.path.join(
            app.config['SESSION_FOLDER'], '{}{}.req'.format(
                app.config['CSV_INPUT_FILE'][:-4],
                file_suffix
            ))
    logging.info('Write to output file: {}'.format(output_file))

    content_list = []
    constants_list = []
    constraints_list = []
    with open(output_file, mode='w') as out_file:
        # Parse variables and variable constraints.
        for var in var_collection.collection.values():
            if var.name in available_vars:
                if var.type in ['CONST', 'ENUMERATOR_INT', 'ENUMERATOR_REAL']:
                    constants_list.append('CONST {} IS {}'.format(var.name, var.value))
                else:
                    content_list.append('Input {} IS {}'.format(
                        var.name,
                        boogie_parsing.BoogieType.reverse_alias(var.type).name
                    ))
                try:
                    for index, constraint in var.constraints.items():
                        if constraint.scoped_pattern is None:
                            continue
                        if constraint.scoped_pattern.get_scope_slug().lower() == 'none':
                            continue
                        if constraint.scoped_pattern.get_pattern_slug() in ['NotFormalizable', 'None']:
                            continue
                        if len(constraint.get_string()) == 0:
                            continue
                        constraints_list.append('Constraint_{}_{}: {}'.format(
                            re.sub(r"\s+", '_', var.name),
                            index,
                            constraint.get_string()
                        ))
                except:
                    pass
        content_list.sort()
        constants_list.sort()
        constraints_list.sort()

        content = '\n'.join(content_list)
        constants = '\n'.join(constants_list)
        constraints = '\n'.join(constraints_list)

        if len(constants) > 0:
            content = '\n\n'.join([constants, content])
        if len(constraints) > 0:
            content = '\n\n'.join([content, constraints])
        content += '\n\n'

        # parse requirement formalizations.
        if not variables_only:
            used_slugs = set()
            for requirement in requirements:  # type: Requirement
                try:
                    for index, formalization in requirement.formalizations.items():
                        slug, used_slugs = clean_identifier_for_ultimate_parser(requirement.rid, used_slugs)
                        if formalization.scoped_pattern is None:
                            continue
                        if formalization.scoped_pattern.get_scope_slug().lower() == 'none':
                            continue
                        if formalization.scoped_pattern.get_pattern_slug() in ['NotFormalizable', 'None']:
                            continue
                        if len(formalization.get_string()) == 0:
                            # formalizatioin string is empty if expressions are missing or none set. Ignore in output
                            continue
                        content += '{}_{}: {}\n'.format(
                            slug,
                            index,
                            formalization.get_string()
                        )
                except AttributeError:
                    continue
        content += '\n'
        out_file.write(content)

    return output_file


def get_stored_session_names(session_folder=None, only_names=False, with_revisions=False) -> tuple:
    """ Get stored session tags (folder names) including os.stat.
    Returned tuple is (
        (os.stat(), name),
        ...
    )
    If only_names == True the tuple is (
        name_1,
        ...
    )
    If with_with_revisions == True the tuple is (
        {
            name: 'name_1',
            'revisions': [revision_1, ...],
            revisions_stats: {
                revision_1: {
                    name: 'revision_1',
                    last_mod: "%A %d. %B %Y at %X" formatted mtime,
                    num_vars: Number of variables used in this revision.
                }
            }
        },
        ...
    )

    :param session_folder: path to folder
    :type session_folder: str
    :return: tuple  of folder names or stats with names
    :rtype: tuple
    """
    result = ()
    if not session_folder:
        session_folder = os.path.join(here, 'data')

    try:
        result = [
            (os.path.join(session_folder, file_name), file_name)
            for file_name in os.listdir(session_folder)
            if os.path.isdir(os.path.join(session_folder, file_name))
        ]
        if with_revisions:
            result = (
                {
                    'name': entry[1],
                    'revisions': get_available_revisions(None, entry[0]),
                    'revisions_stats': get_revisions_with_stats(entry[0])
                } for entry in result
            )
        elif only_names:
            result = (entry[1] for entry in result)
        else:
            result = ((os.stat(entry[0]), entry[1]) for entry in result)
    except Exception as e:
        logging.error('Could not fetch stored sessions: {}'.format(e))

    return result


def get_revisions_with_stats(session_path):
    """ Get meta information about available revisions for a given session path.

    Returns a dict with revision name as key for each revision.
    Each item is then a dict like:
        {
            name: 'revision_1',
            last_mod: %A %d. %B %Y at %X formatted mtime,
            num_vars: 9001
        }


    :param session_path: { revision_1: { name: 'revision_1', last_mod: %A %d. %B %Y at %X, num_vars: 9001} ... }
    """
    revisions = get_available_revisions(None, session_path)
    revisions_stats = dict()
    for revision in revisions:
        revision_path = os.path.join(session_path, revision)
        revision_var_collection_path = os.path.join(
            revision_path,
            'session_variable_collection.pickle'
        )
        try:
            num_vars = len(VariableCollection.load(revision_var_collection_path).collection)
        except:
            num_vars = -1

        revisions_stats[revision] = {
            'name': revision,
            'last_mod': get_last_edit_from_path(revision_path),
            'num_vars': num_vars
        }
    return revisions_stats


def get_last_edit_from_path(path_str):
    """ Return a human readable form of the last edit (mtime) for a path.

    :param path_str: str to path.
    :return: "%A %d. %B %Y at %X" formatted mtime
    """
    return datetime.datetime.fromtimestamp(os.stat(path_str).st_mtime).strftime("%A %d. %B %Y at %X")


def get_available_revisions(config, folder=None):
    """ Returns available revisions for a given session folder.
    Uses config['SESSION_FOLDER'] if no explicit folder is given.

    :param config:
    :param folder:
    :return:
    """
    result = []

    if folder is None:
        folder = config['SESSION_FOLDER']

    try:
        names = os.listdir(folder)
        result = [name for name in names if os.path.isdir(os.path.join(folder, name))]
    except Exception as e:
        logging.error('Could not fetch stored revisions: {}'.format(e))

    return result


def enable_logging(log_level=logging.ERROR, to_file=False, filename='reqtransformer.log'):
    """ Enable Logging.

    :param log_level: Log level
    :type log_level: int
    :param to_file: Wether output should be stored in a file.
    :type to_file: bool
    :param filename: Filename to log to.
    :type filename: str
    """
    if to_file:
        logging.basicConfig(
            format='%(asctime)s: [%(levelname)s]: %(message)s',
            filename=filename,
            level=log_level)
    else:
        logging.basicConfig(
            format='%(asctime)s: [%(levelname)s]: %(message)s',
            level=log_level)
    logging.debug('Enabled logging.')


def setup_logging(app):
    """ Initializes logging with settings from the config.

    """
    if app.config['LOG_LEVEL'] == 'DEBUG':
        log_level = logging.DEBUG
    elif app.config['LOG_LEVEL'] == 'INFO':
        log_level = logging.INFO
    elif app.config['LOG_LEVEL'] == 'WARNING':
        log_level = logging.WARNING
    else:
        log_level = logging.ERROR

    enable_logging(
        log_level=log_level,
        to_file=app.config['LOG_TO_FILE'],
        filename=app.config['LOG_FILE']
    )


def register_assets(app):
    bundles = {
        'css': Bundle(
            'css/bootstrap.css',
            'css/bootstrap-grid.css',
            'css/bootstrap-reboot.css',
            'css/dataTables.bootstrap4.css',
            'css/select.bootstrap4.css',
            'css/tether.css',
            'css/jquery-ui.css',
            'css/bootstrap-tokenfield.css',
            'css/app.css',
            filters='cssutils',
            output='gen/style.css'
        )
    }

    assets = Environment(app)
    assets.register(bundles)


def get_datatable_additional_cols(app):
    offset = 8  # we have 8 fixed cols.
    result = list()
    session_dict = pickle_load_from_dump(app.config['SESSION_STATUS_PATH'])  # type: dict

    for index, name in enumerate(session_dict['csv_fieldnames']):
        result.append(
            {
                'target': index + offset,
                'csv_name': 'csv_data.{}'.format(name),
                'table_header_name': 'csv: {}'.format(name)
            }
        )

    return {'col_defs': result}


def add_msg_to_flask_session_log(app, msg, rid=None, rid_list=None, clear=False, max_msg=50) -> None:
    """ Add a log message for the frontend_logs.

    :param max_msg: Max number of messages to keep in the log.
    :param rid_list: A list of affected requirement IDs
    :param rid: Affected requirement id
    :param app: The flask app
    :param msg: Log message string
    :param clear: Turncate the logs if set to true (false on default).
    """
    session = pickle_load_from_dump(app.config['FRONTEND_LOGS_PATH'])  # type: dict
    template = '[{timestamp}] {message}'

    if rid is not None:
        template += ' <a class="req_direct_link" href="#" data-rid="{rid}">{rid}</a>'

    if rid_list is not None:
        template += ','.join([
            ' <a class="req_direct_link" href="#" data-rid="{rid}">{rid}</a>'.format(rid=rid) for rid in rid_list
        ])

    session['hanfor_log'].append(template.format(
            timestamp=datetime.datetime.now(),
            message=msg,
            rid=rid)
    )

    # Remove oldest logs until threshold
    while len(session['hanfor_log']) > max_msg:
        session['hanfor_log'].pop(0)

    pickle_dump_obj_to_file(session, app.config['FRONTEND_LOGS_PATH'])


def get_flask_session_log(app, html=False) -> Union[list, str]:
    """ Get the frontent log messages from frontend_logs.

    :param app: The flask app
    :param html: Return formatted html version.
    :return: list of messages or html string in case `html == True`
    """
    session = pickle_load_from_dump(app.config['FRONTEND_LOGS_PATH'])  # type: dict
    result = list()
    if 'hanfor_log' in session:
        result = session['hanfor_log']

    if html:
        tmp = ''
        for msg in result:
            tmp += '<p>{}</p>'.format(msg)
        result = tmp

    return result


def slugify(s):
    """ Normalizes string, converts to lowercase, removes non-alpha characters, and converts spaces to hyphens.

    :param s: string
    :type s: str
    :return: String save for filename
    :rtype: str
    """
    s = str(s).strip().replace(' ', '_')
    return re.sub(r'(?u)[^-\w.]', '', s)


class PrefixMiddleware(object):
    ''' Support for url prefixes. '''

    def __init__(self, app, prefix=''):
        self.app = app
        self.prefix = prefix

    def __call__(self, environ, start_response):
        if environ['PATH_INFO'].startswith(self.prefix):
            environ['PATH_INFO'] = environ['PATH_INFO'][len(self.prefix):]
            environ['SCRIPT_NAME'] = self.prefix
            return self.app(environ, start_response)
        else:
            start_response('404', [('Content-Type', 'text/plain')])
            return ["Sorry, this url does not belong to Hanfor.".encode()]


class ListStoredSessions(argparse.Action):
    """ List available session tags. """

    def __init__(self, option_strings, app, dest, *args, **kwargs):
        self.app = app
        super(ListStoredSessions, self).__init__(
            option_strings=option_strings, dest=dest, *args, **kwargs)

    def __call__(self, *args, **kwargs):
        entries = get_stored_session_names(self.app.config['SESSION_BASE_FOLDER'])
        data = []
        data.append(['Tag', 'Created'])
        for entry in entries:
            date_string = datetime.datetime.fromtimestamp(entry[0].st_mtime).strftime("%A %d. %B %Y at %X")
            data.append([entry[1], date_string])
        print('Stored sessions: ')
        if len(data) > 1:
            print(DoubleTable(data).table)
        else:
            print('No sessions in found.')
        exit(0)


class GenerateScopedPatternTrainingData(argparse.Action):
    """ Generate training data consisting of requirement descriptions with assigned scoped pattern."""
    def __init__(self, option_strings, app, dest, *args, **kwargs):
        self.app = app
        super(GenerateScopedPatternTrainingData, self).__init__(
            option_strings=option_strings, dest=dest, *args, **kwargs)

    def __call__(self, *args, **kwargs):
        # logging.debug(self.app.config)
        entries = get_stored_session_names(self.app.config['SESSION_BASE_FOLDER'])
        result = dict()
        for entry in entries:
            logging.debug('Looking into {}'.format(entry[1]))
            current_session_folder = os.path.join(self.app.config['SESSION_BASE_FOLDER'], entry[1])
            revisions = get_available_revisions(self.app.config, folder=current_session_folder)
            for revision in revisions:
                current_revision_folder = os.path.join(current_session_folder, revision)
                logging.debug('Processing `{}`'.format(current_revision_folder))
                requirements = get_requirements(current_revision_folder)
                logging.debug('Found {} requirements .. fetching the formalized ones.'.format(len(requirements)))
                used_slugs = set()
                for requirement in requirements:
                    try:
                        if len(requirement.description) == 0:
                            continue
                        slug, used_slugs = clean_identifier_for_ultimate_parser(requirement.rid, used_slugs)
                        result[slug] = dict()
                        result[slug]['desc'] = requirement.description
                        for index, formalization in requirement.formalizations.items():
                            if formalization.scoped_pattern is None:
                                continue
                            if formalization.scoped_pattern.get_scope_slug().lower() == 'none':
                                continue
                            if formalization.scoped_pattern.get_pattern_slug() in ['NotFormalizable', 'None']:
                                continue
                            if len(formalization.get_string()) == 0:
                                # formalization string is empty if expressions are missing or none set. Ignore in output
                                continue
                            f_key = 'formalization_{}'.format(index)
                            result[slug][f_key] = dict()
                            result[slug][f_key]['scope'] = formalization.scoped_pattern.get_scope_slug()
                            result[slug][f_key]['pattern'] = formalization.scoped_pattern.get_pattern_slug()
                            result[slug][f_key]['formalization'] = formalization.get_string()
                    except AttributeError:
                        continue
            with open('training_data.json', mode='w', encoding='utf-8') as f:
                json.dump(result, f)
        exit(0)


class HanforArgumentParser(argparse.ArgumentParser):
    def __init__(self, app):
        super().__init__()
        self.app = app
        self.add_argument("tag", help="A tag for the session. Session will be reloaded, if tag exists.")
        self.add_argument("-c", "--input_csv", help="Path to the csv to be processed.")
        self.add_argument(
            "-r", "--revision",
            action="store_true",
            help="Create a new session by updating a existing session with a new csv file."
        )
        self.add_argument(
            "-rti", "--reload_type_inference",
            action="store_true",
            help="Reload the type inference results."
        )
        self.add_argument(
            '-L', '--list_stored_sessions',
            nargs=0,
            help="List the tags of stored sessions..",
            action=ListStoredSessions,
            app=self.app
        )
        self.add_argument(
            '-G', '--generate_scoped_pattern_training_data',
            nargs=0,
            help="Generate training data out of description with assigned scoped pattern.",
            action=GenerateScopedPatternTrainingData,
            app=self.app
        )


class MetaSettings():
    """ Just an auto saving minimal dict. """
    def __init__(self, path):
        self.__dict__ = pickle_load_from_dump(path)  # type: dict
        self.path = path

    def update_storage(self):
        pickle_dump_obj_to_file(self.__dict__, self.path)

    def __contains__(self, item):
        return self.__dict__.__contains__(item)

    def __setitem__(self, key, value):
        self.__dict__.__setitem__(key, value)

    def __getitem__(self, item):
        return self.__dict__.__getitem__(item)
